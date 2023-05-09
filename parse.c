#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <string.h>
#include <math.h>
#define MAXWORDS 10000

// variables for keeping track of the data
int ns, data, totn, totl, maxsenlen, maxwordlen, *layers, *nodes, **sentences, **covered, **code, words, (**wordpos)[2], wordlen[MAXWORDS], wordcount[MAXWORDS], *seenalready, ***knowncodes;
char **dictionary;
// variables for algebraic projection
int ng, ni, *imin, *iminmin, *imin_pi, gpi, gpimin, ***bpl, ***bpr;
double *bpld, *bprd;
// variables for clustering
int **wordcluster_size, **wordcluster_number;
double **wordcluster_err, ****wordcluster_center;
// variables involved in the main iteration
double beta, *****v, *****vA, ****vB, *****vR, err, besterr, *worderr, totworderr, **layererr, totlayererr, **biterr;
// file names
char errfile[100], statsfile[100], lexfile[100], treesfile[100];
// options
int ng = 3;        // number of generators/base types/bytes; 3 is standard but more can be useful if using nwc>1 (see below)
int ni = 3;        // number of bits per byte; 3 is standard (a base type, its left inverse, and its right inverse)
int nwc = 1;       // number of clusters to allow per word (must be at least 1, can be more if words have homographs)
int bitflip = 0;   // number of bit flips to allow in branching events (0, 1, 2)
int multibase = 0; // whether to allow multiple base types per category vector (0 for no, 1 for yes)
int rootbits = 0;  // number of "on" bits to allow in root node (0 for identity)
int only1pi = 0;   // whether to limit each layer to at most 1 pair insertion (0 for no, 1 for yes)

static inline double sq(double diff)
{
    return diff * diff;
}

double urand()
{
    return ((double)rand()) / RAND_MAX;
}

// find the best choice of type vector to preserve at each node from one layer to the next
void preserve(int n1, int n2, double ****vo)
{
    int n, g, i;
    for (n = 0; n < n2 - n1 - 1; ++n)
    {
        bpld[n] = 0.;
        bprd[n] = 0.;
        for (g = 0; g < ng; ++g)
            for (i = 0; i < ni; ++i)
            {
                if (vo[n1 + n][1][g][i] + vo[n2 + n][0][g][i] >= 1.)
                {
                    bpl[n][g][i] = 1;
                    bpld[n] += 1. - vo[n1 + n][1][g][i] - vo[n2 + n][0][g][i];
                }
                else
                    bpl[n][g][i] = 0;
                if (vo[n1 + 1 + n][1][g][i] + vo[n2 + 2 + n][0][g][i] >= 1.)
                {
                    bpr[n][g][i] = 1;
                    bprd[n] += 1. - vo[n1 + 1 + n][1][g][i] - vo[n2 + 2 + n][0][g][i];
                }
                else
                    bpr[n][g][i] = 0;
            }
    }
}

// find the distance-minimizing algebraic assignment such that A = BC
double contract(int l, double **voA, double **voB, double **voC)
{
    int g, i;
    double delta, dmin, dist = 0., delta_pi, dmin_pi, best_pi = 0.;
    gpi = -1;
    for (g = 0; g < ng; ++g)
    {
        dmin = 0.;
        // A and B must agree on the leftmost i bits
        // A and C must agree on all subsequent bits
        // start with i=0
        for (i = 0; i < ni; ++i)
            if (voA[g][i] + voC[g][i] >= 1.)
                dmin += 1. - voA[g][i] - voC[g][i];
        dmin_pi = dmin;
        imin[g] = 0;
        imin_pi[g] = 0;
        delta = 0.;
        delta_pi = 0.;
        // now loop over i>=1 and do the same:
        for (i = 1; i <= ni; ++i)
        {
            // zero out the i-1 bit between A & C
            if (voA[g][i - 1] + voC[g][i - 1] >= 1.)
            {
                delta -= 1. - voA[g][i - 1] - voC[g][i - 1];
                delta_pi -= 1. - voA[g][i - 1] - voC[g][i - 1];
            }
            // then make A & B agree on the i-1 bit
            if (voA[g][i - 1] + voB[g][i - 1] >= 1.)
            {
                delta += 1. - voA[g][i - 1] - voB[g][i - 1];
                delta_pi += 1. - voA[g][i - 1] - voB[g][i - 1];
            }
            // now remove the previous element-and-its-inverse pair, if applicable
            if (i > 1 && voB[g][i - 1] + voC[g][i - 2] >= 1.)
                delta_pi -= 1. - voB[g][i - 1] - voC[g][i - 2];
            // and insert an element-and-its-inverse pair, if the distance is favorable
            if (i != ni && voB[g][i] + voC[g][i - 1] >= 1.)
                delta_pi += 1. - voB[g][i] - voC[g][i - 1];
            // delta compares the distance for this i to the distance for the last i that was optimal
            if (delta < 0)
            { // so if delta < 0, this i is the new optimal choice
                dmin += delta;
                delta = 0;
                imin[g] = i;
            }
            // delta_pi compares the distances if insertion is allowed
            if (delta_pi < 0)
            { // so if delta_pi < 0, this i is the new optimal choice allowing insertion
                dmin_pi += delta_pi;
                delta_pi = 0;
                imin_pi[g] = i;
            }
        }
        if (only1pi)
            dist += dmin;
        else
            dist += dmin_pi < dmin ? dmin_pi : dmin;
        if (dmin_pi - dmin < best_pi) // if this is the best inverse-pair
        {
            gpi = g;
            best_pi = dmin_pi - dmin;
        }
    }
    if (only1pi && best_pi < 0) // if the best pair insertion actually did reduce the distance
        dist += best_pi;
    return dist;
}

// find the best choice of type vectors to relate one layer to the next:
// one of the vectors in the layer below must be equal to the product of the two vectors jut above it
// and the remaining vectors to the left and right of the contraction must be preserved
void layerproj(int d, int l, double ****vo)
{
    int nmin, n, n1 = l * (l + 1) / 2, n2 = n1 + l + 1, g, i, b;
    double delta, dn, dp;

    preserve(n1, n2, vo);
    dp = contract(l, vo[n1][1], vo[n2][0], vo[n2 + 1][0]);
    nmin = 0;
    for (g = 0; g < ng; ++g)
    {
        if (!only1pi || g == gpi)    // if this is the byte has a pair insertion
            iminmin[g] = imin_pi[g]; // then use the corresponding bit position
        else
            iminmin[g] = imin[g];
    }
    gpimin = gpi;
    delta = 0.;
    for (n = 1; n < l; ++n)
    {
        dn = contract(l, vo[n1 + n][1], vo[n2 + n][0], vo[n2 + 1 + n][0]);
        delta += dn - dp + bpld[n - 1] - bprd[n - 1];
        dp = dn;
        if (delta < 0.)
        {
            delta = 0;
            nmin = n;
            for (g = 0; g < ng; ++g)
            {
                if (!only1pi || g == gpi)
                    iminmin[g] = imin_pi[g];
                else
                    iminmin[g] = imin[g];
            }
            gpimin = gpi;
        }
    }

    // preserve the type vectors to the left of the branching point
    for (n = 0; n < nmin; ++n)
        for (g = 0; g < ng; ++g)
            for (i = 0; i < ni; ++i)
            {
                vA[d][n1 + n][1][g][i] = 1. * bpl[n][g][i];
                vA[d][n2 + n][0][g][i] = 1. * bpl[n][g][i];
            }
    // preserve the type vectors to the right of the branching point
    for (n = nmin; n < l; ++n)
        for (g = 0; g < ng; ++g)
            for (i = 0; i < ni; ++i)
            {
                vA[d][n1 + 1 + n][1][g][i] = 1. * bpr[n][g][i];
                vA[d][n2 + 2 + n][0][g][i] = 1. * bpr[n][g][i];
            }
    for (g = 0; g < ng; ++g)
    {
        for (i = 0; i < iminmin[g]; ++i)
        { // preserve the bits to the left of the multiplication
            b = (vo[n1 + nmin][1][g][i] + vo[n2 + nmin][0][g][i] >= 1.);
            vA[d][n1 + nmin][1][g][i] = 1. * b;
            vA[d][n2 + nmin][0][g][i] = 1. * b;
        }
        for (i = iminmin[g]; i < ni; ++i)
        { // preserve the bits to the right of the multiplication
            b = (vo[n1 + nmin][1][g][i] + vo[n2 + 1 + nmin][0][g][i] >= 1.);
            vA[d][n1 + nmin][1][g][i] = 1. * b;
            vA[d][n2 + 1 + nmin][0][g][i] = 1. * b;
        }
        if (iminmin[g] == 0)
        {
            for (i = 0; i < ni; ++i)
                vA[d][n2 + nmin][0][g][i] = 0.;
            continue;
        }
        if (iminmin[g] == ni)
        {
            for (i = 0; i < ni; ++i)
                vA[d][n2 + 1 + nmin][0][g][i] = 0.;
            continue;
        }
        // insert a cancellative pair of bits...
        if (only1pi && g != gpimin) // ...but only if allowed here...
            b = 0;
        else // ...and only if the distance is favorable
            b = vo[n2 + nmin][0][g][iminmin[g]] + vo[n2 + 1 + nmin][0][g][iminmin[g] - 1] >= 1.;
        vA[d][n2 + nmin][0][g][iminmin[g]] = 1. * b;
        vA[d][n2 + 1 + nmin][0][g][iminmin[g] - 1] = 1. * b; // seg fault
        // zero out all other bits
        for (i = iminmin[g] + 1; i < ni; ++i)
            vA[d][n2 + nmin][0][g][i] = 0.;
        for (i = 0; i < iminmin[g] - 1; ++i)
            vA[d][n2 + 1 + nmin][0][g][i] = 0.;
    }

    if (bitflip == 1)
    { // allow a bit flip in one of the vectors above the expansion
        int maxdist, nmax, gmax, imax;
        for (g = 0; g < ng; ++g)
            for (i = 0; i < ni; ++i)
                if (g + i == 0 || sq(vA[d][n2 + nmin][0][g][i] - vo[n2 + nmin][0][g][i]) > maxdist)
                {
                    maxdist = sq(vA[d][n2 + nmin][0][g][i] - vo[n2 + nmin][0][g][i]);
                    gmax = g;
                    imax = i;
                    nmax = 0;
                }
        for (g = 0; g < ng; ++g)
            for (i = 0; i < ni; ++i)
                if (sq(vA[d][n2 + 1 + nmin][0][g][i] - vo[n2 + 1 + nmin][0][g][i]) > maxdist)
                {
                    maxdist = sq(vA[d][n2 + 1 + nmin][0][g][i] - vo[n2 + 1 + nmin][0][g][i]);
                    gmax = g;
                    imax = i;
                    nmax = 1;
                }
        vA[d][n2 + nmax + nmin][0][gmax][imax] = (vo[n2 + nmax + nmin][0][gmax][imax] >= .5);
    }
    if (bitflip == 2)
    { // allow a bit flip in both of the vectors above the expansion
        int maxdist, gmax, imax;
        for (g = 0; g < ng; ++g)
            for (i = 0; i < ni; ++i)
                if (g + i == 0 || sq(vA[d][n2 + nmin][0][g][i] - vo[n2 + nmin][0][g][i]) > maxdist)
                {
                    maxdist = sq(vA[d][n2 + nmin][0][g][i] - vo[n2 + nmin][0][g][i]);
                    gmax = g;
                    imax = i;
                }
        vA[d][n2 + nmin][0][gmax][imax] = (vo[n2 + nmin][0][gmax][imax] >= .5);
        for (g = 0; g < ng; ++g)
            for (i = 0; i < ni; ++i)
                if (g + i == 0 || sq(vA[d][n2 + 1 + nmin][0][g][i] - vo[n2 + 1 + nmin][0][g][i]) > maxdist)
                {
                    maxdist = sq(vA[d][n2 + 1 + nmin][0][g][i] - vo[n2 + 1 + nmin][0][g][i]);
                    gmax = g;
                    imax = i;
                }
        vA[d][n2 + 1 + nmin][0][gmax][imax] = (vo[n2 + 1 + nmin][0][gmax][imax] >= .5);
    }
}

// calculate the squared distance between two lexical vectors
double vdist(double **v1, double **v2)
{
    int g, i;
    double dist = 0.;
    for (g = 0; g < ng; g++)
        for (i = 0; i < ni; i++)
            dist += sq(v1[g][i] - v2[g][i]);
    return dist;
}

// make initial guesses for the word cluster centers
void initializewordclusters(int w, double *****vo)
{
    int u, d, n, g, i, c, c_assigned, dmax, nmax;
    double dist, totdist, maxdist, p, p0;
    // choose first center at random
    u = (int)(urand() * wordcount[w]);
    d = wordpos[w][u][0];
    n = wordpos[w][u][1];
    for (g = 0; g < ng; g++)
        for (i = 0; i < ni; i++)
            wordcluster_center[w][c][g][i] = vo[d][n][1][g][i];
    c_assigned = 1;
    while (c_assigned < wordcount[w] && c_assigned < nwc)
    {
        totdist = 0.;
        // find distance for all other points
        for (u = 0; u < wordcount[w]; ++w)
        {
            d = wordpos[w][u][0];
            n = wordpos[w][u][1];
            dist = 0.;
            for (c = 0; c < c_assigned; c++)
                dist += vdist(wordcluster_center[w][c], vo[d][n][1]);
            totdist += dist;
            if (u == 0 || dist > maxdist)
            {
                dmax = d;
                nmax = n;
                maxdist = dist;
            }
        }
        // pick a new center based on distance
        /*for (g = 0; g < ng; g++)
            for (i = 0; i < ni; i++)
                wordcluster_center[w][c_assigned][g][i] = vo[dmax][nmax][1][g][i];
        c_assigned++;*/
        p0 = urand();
        p = 0.;
        for (u = 0; u < wordcount[w]; ++w)
        {
            d = wordpos[w][u][0];
            n = wordpos[w][u][1];
            dist = 0.;
            for (c = 0; c < c_assigned; c++)
                dist += vdist(wordcluster_center[w][c], vo[d][n][1]);
            p += dist / totdist;
            if (p >= p0)
            {
                for (g = 0; g < ng; g++)
                    for (i = 0; i < ni; i++)
                        wordcluster_center[w][c_assigned][g][i] = vo[d][n][1][g][i];
                c_assigned++;
                u = wordcount[w];
                break;
            }
        }
    }
}

// iterate the word clustering method:
// find the closest cluster center for each point,
// then make the new cluster centers the averages of their new member points;
// returns the number of points that have changed membership
int iteratewordcluster(int w, double *****vo)
{
    int u, d, n, nn, g, i, c, bc, changes = 0;
    double dist, mindist;
    for (u = 0; u < wordcount[w]; u++)
    {
        d = wordpos[w][u][0];
        n = wordpos[w][u][1];
        nn = n - layers[d] * (layers[d] + 1) / 2;
        for (c = 0; c < nwc; c++) // find the closest cluster center
        {
            dist = vdist(wordcluster_center[w][c], vo[d][n][1]);
            if (c == 0 || dist < mindist)
            {
                bc = c;
                mindist = dist;
            }
        }
        if (bc != wordcluster_number[d][nn])
        { // if this lexical vector has changed its cluster
            wordcluster_number[d][nn] = bc;
            changes++;
        }
    }
    // reset the clusters
    for (c = 0; c < nwc; c++)
    {
        wordcluster_size[w][c] = 0;
        for (g = 0; g < ng; g++)
            for (i = 0; i < ni; i++)
                wordcluster_center[w][c][g][i] = 0.;
    }
    for (u = 0; u < wordcount[w]; u++)
    {
        d = wordpos[w][u][0];
        n = wordpos[w][u][1];
        nn = n - layers[d] * (layers[d] + 1) / 2;
        wordcluster_size[w][wordcluster_number[d][nn]]++;
        for (g = 0; g < ng; g++)
            for (i = 0; i < ni; i++)
                wordcluster_center[w][wordcluster_number[d][nn]][g][i] += vo[d][n][1][g][i];
    }
    for (c = 0; c < nwc; c++)
        if (wordcluster_size[w][c])
            for (g = 0; g < ng; g++)
                for (i = 0; i < ni; i++)
                    wordcluster_center[w][c][g][i] /= wordcluster_size[w][c];
    return changes;
}

// groups the top layer nodes associated with each word into nwc clusters
void wordcluster(double *****vo)
{
    int w, u, d, n, nn, g, i, c;

    for (w = 0; w < words; w++)
    {
        if (seenalready[w]) // if we know this word from our existing solution, then we use the code we know
        {
            for (u = 0; u < wordcount[w]; u++)
                for (g = 0; g < ng; g++)
                    for (i = 0; i < ni; i++)
                        vA[wordpos[w][u][0]][wordpos[w][u][1]][1][g][i] = 1. * knowncodes[w][g][i];
            continue;
        }
        // otherwise, carry on as usual
        // initialize the word clusters
        initializewordclusters(w, vo);
        i = 0;
        while (i < 10 && iteratewordcluster(w, vo))
            i++;
        for (u = 0; u < wordcount[w]; u++)
        {
            d = wordpos[w][u][0];
            n = wordpos[w][u][1];
            nn = n - layers[d] * (layers[d] + 1) / 2;
            for (g = 0; g < ng; g++)
                for (i = 0; i < ni; i++)
                    vA[d][n][1][g][i] = wordcluster_center[w][wordcluster_number[d][nn]][g][i];
        }
    }
}

void startconcur(double *****vo)
{
    int d, g, i;
    if (rootbits == 0)
        for (d = 0; d < data; ++d)
            for (g = 0; g < ng; ++g)
                for (i = 0; i < ni; ++i)
                    vB[d][0][g][i] = 0.;
    else
    {
        double bitsum, adjustment;
        for (d = 0; d < data; ++d)
        {
            bitsum = 0.;
            for (g = 0; g < ng; ++g)
                for (i = 0; i < ni; ++i)
                {
                    vB[d][0][g][i] = vo[d][0][1][g][i];
                    bitsum += vB[d][0][g][i];
                }
            if (bitsum > rootbits)
            {
                adjustment = (rootbits - bitsum) / ng / ni;
                for (g = 0; g < ng; ++g)
                    for (i = 0; i < ni; ++i)
                        vB[d][0][g][i] += adjustment;
            }
        }
    }
}

void nodeconcur(double *****vo)
{
    int d, l, n, g, i, middle = (ni - 1) / 2;
    double bitsum, target, adjustment;

    for (d = 0; d < data; ++d)
    {
        for (l = 1; l < layers[d]; ++l)
            for (n = l * (l + 1) / 2; n < (l + 1) * (l + 2) / 2; ++n)
            { // make sure upward and downward type vectors agree at each node
                bitsum = 0.;
                target = (n + 1 != (l + 1) * (l + 2) / 2); // want one central bit on, except at end node (punctuation)
                for (g = 0; g < ng; ++g)
                {
                    for (i = 0; i < ni; ++i)
                        vB[d][n][g][i] = (vo[d][n][0][g][i] + vo[d][n][1][g][i]) / 2.;
                    bitsum += vB[d][n][g][middle];
                }
                if (!multibase || bitsum < target)
                {
                    adjustment = (target - bitsum) / ng;
                    for (g = 0; g < ng; ++g)
                        vB[d][n][g][middle] += adjustment;
                }
            }
        // treat the top layer separately
        l = layers[d];
        for (n = l * (l + 1) / 2; n < (l + 1) * (l + 2) / 2; ++n)
        { // make sure upward and downward type vectors agree at each node
            bitsum = 0.;
            target = (n + 1 != (l + 1) * (l + 2) / 2); // want one central bit on, except at end node (punctuation)
            for (g = 0; g < ng; ++g)
            {
                for (i = 0; i < ni; ++i)
                    vB[d][n][g][i] = (vo[d][n][0][g][i] + vo[d][n][1][g][i]) / 2.;
                bitsum += vB[d][n][g][middle];
            }
            if (!multibase || bitsum < target)
            {
                adjustment = (target - bitsum) / ng;
                for (g = 0; g < ng; ++g)
                    vB[d][n][g][middle] += adjustment;
            }
        }
    }
}

void projA(double *****vo)
{
    int d, l;
    wordcluster(vo);
    for (d = 0; d < data; ++d)
        for (l = 0; l < layers[d]; ++l)
            layerproj(d, l, vo[d]);
}

void projB(double *****vo)
{
    startconcur(vo);
    nodeconcur(vo);
}

void ref(double *****vo)
{
    int d, n, k, g, i;
    for (d = 0; d < data; d++)
        for (n = 0; n < nodes[d]; n++)
            for (k = 0; k < 2; k++)
                for (g = 0; g < ng; g++)
                    for (i = 0; i < ni; i++)
                        vR[d][n][k][g][i] = 2. * vo[d][n][k][g][i] - v[d][n][k][g][i];
}

void iterate()
{
    int d, l, n, k, g, i, w, u, count;
    double diff;

    projA(v);
    ref(vA);
    projB(vR);

    totworderr = 0.;
    for (w = 0; w < words; w++)
        worderr[w] = 0.;
    totlayererr = 0.;
    for (d = 0; d < data; d++)
        for (l = 0; l < layers[d]; ++l)
            layererr[d][l] = 0.;
    for (g = 0; g < ng; g++)
        for (i = 0; i < ni; i++)
            biterr[g][i] = 0.;
    for (d = 0; d < data; ++d)
        for (g = 0; g < ng; ++g)
            for (i = 0; i < ni; ++i)
            {
                for (l = 0; l < layers[d]; ++l)
                {
                    for (n = l * (l + 1) / 2; n < (l + 1) * (l + 2) / 2; ++n)
                    {
                        diff = vB[d][n][g][i] - vA[d][n][1][g][i];
                        v[d][n][1][g][i] += beta * diff;
                        layererr[d][l] += sq(diff);
                        biterr[g][i] += sq(diff);
                    }
                    for (n = (l + 1) * (l + 2) / 2; n < (l + 2) * (l + 3) / 2; ++n)
                    {
                        diff = vB[d][n][g][i] - vA[d][n][0][g][i];
                        v[d][n][0][g][i] += beta * diff;
                        layererr[d][l] += sq(diff);
                        biterr[g][i] += sq(diff);
                    }
                }
                for (n = layers[d] * (layers[d] + 1) / 2; n < (layers[d] + 1) * (layers[d] + 2) / 2; ++n)
                {
                    diff = vB[d][n][g][i] - vA[d][n][1][g][i];
                    v[d][n][1][g][i] += beta * diff;
                    worderr[sentences[d][n - layers[d] * (layers[d] + 1) / 2]] += sq(diff);
                    biterr[g][i] += sq(diff);
                }
            }
    for (w = 0; w < words; w++)
    {
        worderr[w] /= wordcount[w] * ng * ni;
        totworderr += worderr[w];
    }
    totworderr /= words;
    for (d = 0; d < data; ++d)
        for (l = 0; l < layers[d]; ++l)
        {
            layererr[d][l] /= (2 * l + 3) * ng * ni;
            totlayererr += layererr[d][l];
        }
    totlayererr /= totl;
    err = (totlayererr + totworderr) / 2.;
    for (g = 0; g < ng; g++)
        for (i = 0; i < ni; i++)
            biterr[g][i] /= 2 * totn - data;
}

void makevars()
{
    int d, n, k, g, w, r, c, nk;

    // variables for keeping track of the data
    wordpos = malloc(words * sizeof(int *[2]));
    int maxwordcount = 0;
    for (w = 0; w < words; w++)
    {
        wordpos[w] = malloc(wordcount[w] * sizeof(int[2]));
        if (wordcount[w] > maxwordcount)
            maxwordcount = wordcount[w];
    }
    sentences = malloc(data * sizeof(int *));
    for (d = 0; d < data; d++)
        sentences[d] = malloc((layers[d] + 1) * sizeof(int));
    covered = malloc(data * sizeof(int *));
    for (d = 0; d < data; d++)
        covered[d] = malloc((layers[d] + 1) * sizeof(int));
    code = malloc(ng * sizeof(int *));
    for (g = 0; g < ng; g++)
        code[g] = malloc(ni * sizeof(int));

    // variables for algebraic projection
    imin = malloc(ng * sizeof(int));
    imin_pi = malloc(ng * sizeof(int));
    iminmin = malloc(ng * sizeof(int));
    bpld = malloc((maxsenlen - 1) * sizeof(double));
    bprd = malloc((maxsenlen - 1) * sizeof(double));
    bpl = malloc((maxsenlen - 1) * sizeof(int **));
    bpr = malloc((maxsenlen - 1) * sizeof(int **));
    for (n = 0; n < maxsenlen - 1; n++)
    {
        bpl[n] = malloc(ng * sizeof(int *));
        bpr[n] = malloc(ng * sizeof(int *));
        for (g = 0; g < ng; g++)
        {
            bpl[n][g] = malloc(ni * sizeof(int));
            bpr[n][g] = malloc(ni * sizeof(int));
        }
    }

    // variables for clustering
    wordcluster_number = malloc(data * sizeof(int *));
    for (d = 0; d < data; d++)
        wordcluster_number[d] = malloc((layers[d] + 1) * sizeof(int));
    wordcluster_size = malloc(words * sizeof(int *));
    wordcluster_err = malloc(words * sizeof(double *));
    wordcluster_center = malloc(words * sizeof(double ***));
    for (w = 0; w < words; w++)
    {
        wordcluster_size[w] = malloc(nwc * sizeof(int));
        wordcluster_err[w] = malloc(nwc * sizeof(double));
        wordcluster_center[w] = malloc(nwc * sizeof(double **));
        for (c = 0; c < nwc; c++)
        {
            wordcluster_center[w][c] = malloc(ng * sizeof(double *));
            for (g = 0; g < ng; g++)
                wordcluster_center[w][c][g] = malloc(ni * sizeof(double));
        }
    }

    // variables involved in the main iteration
    v = malloc(data * sizeof(double ****));
    vA = malloc(data * sizeof(double ****));
    vR = malloc(data * sizeof(double ****));
    vB = malloc(data * sizeof(double ***));

    for (d = 0; d < data; d++)
    {
        v[d] = malloc(nodes[d] * sizeof(double ***));
        vA[d] = malloc(nodes[d] * sizeof(double ***));
        vR[d] = malloc(nodes[d] * sizeof(double ***));
        vB[d] = malloc(nodes[d] * sizeof(double **));

        nk = 2;
        for (n = 0; n < nodes[d]; n++)
        {
            v[d][n] = malloc(nk * sizeof(double **));
            vA[d][n] = malloc(nk * sizeof(double **));
            vR[d][n] = malloc(nk * sizeof(double **));

            for (k = 0; k < nk; k++)
            {
                v[d][n][k] = malloc(ng * sizeof(double *));
                vA[d][n][k] = malloc(ng * sizeof(double *));
                vR[d][n][k] = malloc(ng * sizeof(double *));

                for (g = 0; g < ng; g++)
                {
                    v[d][n][k][g] = malloc(ni * sizeof(double));
                    vA[d][n][k][g] = malloc(ni * sizeof(double));
                    vR[d][n][k][g] = malloc(ni * sizeof(double));
                }
            }

            vB[d][n] = malloc(ng * sizeof(double *));
            for (g = 0; g < ng; ++g)
                vB[d][n][g] = malloc(ni * sizeof(double));
        }
    }

    // errors and metric weights
    worderr = malloc(words * sizeof(double));
    layererr = malloc(data * sizeof(double *));
    for (d = 0; d < data; ++d)
        layererr[d] = malloc(layers[d] * sizeof(double));
    biterr = malloc(ng * sizeof(double *));
    for (g = 0; g < ng; g++)
        biterr[g] = malloc(ni * sizeof(double));
}

int getdata(char *textfile)
{
    FILE *fp;
    int l, n, k, wl, w, c, same, i;
    char ch;

    fp = fopen(textfile, "r");
    if (!fp)
    {
        printf("textfile not found\n");
        return 0;
    }

    data = 0;
    wl = 0;
    maxwordlen = 0;
    // read file once just to figure out how many sentences are available and what the max word length is
    while ((ch = fgetc(fp)) != EOF && data < ns)
    {
        if (ch == ' ' || ch == '\n')
        {
            if (wl > maxwordlen)
                maxwordlen = wl;
            wl = 0;
            if (ch != ' ')
                data++;
        }
        else
            wl++;
    }
    fclose(fp);

    // now we can alloc memory for our dictionary/wordcount and layer/node counts
    dictionary = malloc(MAXWORDS * sizeof(char *));
    for (w = 0; w < MAXWORDS; w++)
    {
        dictionary[w] = malloc((maxwordlen + 1) * sizeof(char));
        wordcount[w] = 1;
    }
    layers = malloc(data * sizeof(int));
    nodes = malloc(data * sizeof(int));

    data = 0;
    l = 0;
    totl = 0;
    totn = 0;
    wl = 0;
    words = 0;
    char word[maxwordlen + 1];
    for (i = 0; i <= maxwordlen; ++i)
        word[i] = 0;
    fp = fopen(textfile, "r");
    maxsenlen = 0;
    // read file again to fill in the dictionary/wordcounts and layer/node counts
    while ((ch = fgetc(fp)) != EOF && data < ns)
    {
        if (ch == ' ' || ch == '\n')
        {
            if (ch == ' ' && wl == 0)
                continue;
            for (w = 0; w < words; ++w)
                if (strcmp(dictionary[w], word) == 0)
                {
                    wordcount[w]++;
                    break;
                }
            if (w == words)
            {
                if (words == MAXWORDS)
                {
                    printf("need bigger dictionary\n");
                    return 0;
                }
                sprintf(dictionary[words], "%s", word);
                wordlen[words] = wl;
                words++;
            }
            if (wl > 0)
            {
                wl = 0;
                l++;
            }
            if (ch == '\n')
            {
                layers[data] = l - 1;
                nodes[data] = l * (l + 1) / 2;
                totl += l - 1;
                totn += l * (l + 1) / 2;
                if (l > maxsenlen)
                    maxsenlen = l;
                l = 0;
                data++;
            }
            for (i = 0; i <= maxwordlen; ++i)
                word[i] = 0;
        }
        else
        {
            word[wl] = ch;
            wl++;
        }
    }
    fclose(fp);

    // now that we know the number of layers and nodes
    // we can allocate memory for all the type vectors and word positions
    makevars();

    fp = fopen(textfile, "r");
    data = 0;
    l = 0;
    wl = 0;
    for (w = 0; w < MAXWORDS; w++)
        wordcount[w] = 0;
    // read file one more time to record the positions in which each word occurs
    while ((ch = fgetc(fp)) != EOF && data < ns)
    {
        if (ch == ' ' || ch == '\n')
        {
            if (ch == ' ' && wl == 0)
                continue;
            for (w = 0; w < words; w++)
                if (strcmp(dictionary[w], word) == 0)
                {
                    sentences[data][l] = w;
                    wordpos[w][wordcount[w]][0] = data;
                    wordpos[w][wordcount[w]][1] = layers[data] * (layers[data] + 1) / 2 + l;
                    wordcount[w]++;
                    break;
                }
            if (wl > 0)
            {
                wl = 0;
                l++;
            }
            if (ch == '\n')
            {
                l = 0;
                data++;
            }
            for (i = 0; i <= maxwordlen; ++i)
                word[i] = 0;
        }
        else
        {
            word[wl] = ch;
            wl++;
        }
    }
    fclose(fp);

    return 1;
}

int readlex(char *seedfile)
{
    FILE *fp;

    fp = fopen(seedfile, "r");
    if (!fp)
    {
        printf("lexicon file not found\n");
        return 0;
    }
    char *line = NULL, *code, *linetokens, *token;
    size_t line_size = 0;
    int numlex = 0, w, g, i;
    seenalready = malloc(words * sizeof(int));
    knowncodes = malloc(words * sizeof(int **));
    for (w = 0; w < words; w++)
    {
        seenalready[w] = 0;
        knowncodes[w] = malloc(ng * sizeof(int *));
        for (g = 0; g < ng; g++)
            knowncodes[w][g] = malloc(ni * sizeof(int));
    }
    while (getline(&line, &line_size, fp) >= 0)
    { // each line in the lex file should be of the form "code : word word word ..."
        code = strtok(line, ":");
        linetokens = strtok(NULL, ":"); // should contain all the words/tokens for this lexical code
        if (linetokens == NULL)
            break;
        linetokens = strtok(linetokens, "\n"); // remove new line character
        token = strtok(linetokens, " ");
        while (token != NULL)
        {
            for (w = 0; w < words; w++)
                if (strcmp(dictionary[w], token) == 0)
                {
                    seenalready[w]++;
                    for (g = 0; g < ng; g++)
                        for (i = 0; i < ni; i++)
                            knowncodes[w][g][i] = code[g * (ni + 1) + i] - '0';
                    break;
                }
            token = strtok(NULL, " ");
        }
        numlex++;
    }
    fclose(fp);
    for (w = 0; w < words; w++)
        if (seenalready[w])
        {
            printf("%s (%d): ", dictionary[w], seenalready[w]);
            for (g = 0; g < ng; g++)
            {
                for (i = 0; i < ni; i++)
                    printf("%d", knowncodes[w][g][i]);
                printf(" ");
            }
            printf("\n");
        }

    return 1;
}

void randstart()
{
    int d, l, n, k, g, i, w, u, c;
    double r;
    // initialize the vectors
    for (d = 0; d < data; ++d)
        for (n = 0; n < nodes[d] - layers[d] - 1; ++n)
            for (k = 0; k < 2; ++k)
                for (g = 0; g < ng; ++g)
                    for (i = 0; i < ni; ++i)
                        v[d][n][k][g][i] = urand();
    // initialize the top layer vectors by word
    for (w = 0; w < words; w++)
        for (g = 0; g < ng; ++g)
            for (i = 0; i < ni; ++i)
            {
                r = urand();
                for (u = 0; u < wordcount[w]; u++)
                    for (k = 0; k < 2; k++)
                        v[wordpos[w][u][0]][wordpos[w][u][1]][k][g][i] = urand(); // r; // to give every instance of a word same start
            }
    // initialize the word clusters
    for (d = 0; d < data; d++)
        for (n = 0; n <= layers[d]; n++)
            wordcluster_number[d][n] = -1;
    for (w = 0; w < words; w++)
    {
        for (c = 0; c < nwc; c++)
            for (g = 0; g < ng; ++g)
                for (i = 0; i < ni; ++i)
                    wordcluster_center[w][c][g][i] = urand();
    }
}

int eqcode(double **vec, int **code)
{
    int g, i;
    for (g = 0; g < ng; g++)
        for (i = 0; i < ni; i++)
            if ((vec[g][i] > .5) != code[g][i])
                return 0;
    return 1;
}

void printlex()
{
    FILE *fp;
    int d, l, g, i, d1, l1;

    for (d = 0; d < data; d++)
        for (l = 0; l <= layers[d]; l++)
            covered[d][l] = 0;

    fp = fopen(lexfile, "w");
    for (d = 0; d < data; d++)
        for (l = 0; l <= layers[d]; l++)
        {
            if (covered[d][l])
                continue;
            // print this code
            for (g = 0; g < ng; ++g)
            {
                for (i = 0; i < ni; ++i)
                {
                    code[g][i] = vB[d][layers[d] * (layers[d] + 1) / 2 + l][g][i] >= .5;
                    fprintf(fp, "%d", code[g][i]);
                }
                fprintf(fp, " ");
            }
            fprintf(fp, ": %s", dictionary[sentences[d][l]]);
            covered[d][l] = 1;
            for (d1 = d; d1 < data; d1++)
                for (l1 = (d1 == d ? l + 1 : 0); l1 <= layers[d1]; l1++)
                    if (!covered[d1][l1] && eqcode(vB[d1][layers[d1] * (layers[d1] + 1) / 2 + l1], code))
                    {
                        fprintf(fp, " %s", dictionary[sentences[d1][l1]]);
                        covered[d1][l1] = 1;
                    }
            fprintf(fp, "\n");
        }
    fprintf(fp, "-------\n");
    fclose(fp);
}

void printtrees()
{
    FILE *fp;
    int d, l, n, g, i, n1, n2;

    fp = fopen(treesfile, "w");
    for (d = 0; d < data; ++d)
    {
        for (g = 0; g < ng; ++g)
        {
            for (i = 0; i < ni; ++i)
                fprintf(fp, "%d", (vB[d][0][g][i] > .5));
            fprintf(fp, " ");
        }
        fprintf(fp, ",\n");
        for (l = 1; l <= layers[d]; ++l)
        {
            for (n = l * (l + 1) / 2; n < (l + 1) * (l + 2) / 2; ++n)
            {
                for (g = 0; g < ng; ++g)
                {
                    for (i = 0; i < ni; ++i)
                        fprintf(fp, "%d", (vB[d][n][g][i] > .5));
                    fprintf(fp, " ");
                }
                fprintf(fp, ", ");
            }
            fprintf(fp, "\n");
        }
        for (n = 0; n <= layers[d]; n++)
            fprintf(fp, " %s", dictionary[sentences[d][n]]);
        fprintf(fp, "\n\n");
    }
    fprintf(fp, "-------\n");
    fclose(fp);
}

int solve(char *errfile, int maxiter, double stoperr)
{
    int iter, d, l, w, g, i;
    besterr = 1.;
    FILE *fp;
    fp = fopen(errfile, "w");
    for (iter = 1; iter <= maxiter && (err >= stoperr || iter == 1); ++iter)
    {
        iterate();
        // print errors by bit
        for (g = 0; g < ng; g++)
        {
            for (i = 0; i < ni; i++)
            {
                fprintf(fp, "%.6f", sqrt(biterr[g][i]));
                if (i + 1 < ni)
                    fprintf(fp, ",");
            }
            if (g + 1 < ng)
                fprintf(fp, ";");
        }
        fprintf(fp, "\n");
        // update solutions if the current error is the lowest yet
        if (err < besterr)
        {
            besterr = err;
            printlex();
            printtrees();
        }
    }
    fclose(fp);
    return (iter - 1) % maxiter;
}

int main(int argc, char *argv[])
{
    char *textfile, *seedfile, *name;
    int iter, maxiter, iterstride, trials, t, c, solcount;
    double stoperr, aveiter, elapsed, avesec;
    FILE *fp;
    clock_t start;

    if (argc == 7)
    {
        textfile = argv[1];
        ns = atoi(argv[2]);
        seedfile = argv[3];
        maxiter = atoi(argv[4]);
        beta = .5;             // iteration speed parameter (should be between 0 and 1)
        stoperr = sq(.000001); // stop iterating if error drops below this
        trials = atoi(argv[5]);
        name = argv[6];
    }
    else
    {
        printf("expected six arguments: textfile, sentences, lexical seed, iterations, trials, name\n");
        return 1;
    }

    sprintf(errfile, "%s.err", name);
    sprintf(statsfile, "%s.stats", name);
    sprintf(lexfile, "%s.lex", name);
    sprintf(treesfile, "%s.trees", name);

    if (!getdata(textfile))
        return 1;
    if (strcmp(seedfile, "noseed") != 0 && !readlex(seedfile))
        return 1;

    fp = fopen(statsfile, "w");
    for (c = 0; c < argc; ++c)
        fprintf(fp, "%s ", argv[c]);
    fprintf(fp, "\n\n");
    fclose(fp);

    srand(time(NULL));
    start = clock();
    solcount = 0;
    aveiter = 0.;
    avesec = 0.;
    for (t = 0; t < trials; ++t)
    {
        randstart();
        sprintf(errfile, "%s%d.err", name, t);
        sprintf(lexfile, "%s%d.lex", name, t);
        sprintf(treesfile, "%s%d.trees", name, t);
        iter = solve(errfile, maxiter, stoperr);
        if (iter)
        {
            ++solcount;
            aveiter += iter;
        }
        else
            aveiter += maxiter;

        fp = fopen(statsfile, "a");
        elapsed = ((double)(clock() - start)) / CLOCKS_PER_SEC;
        avesec += elapsed;
        fprintf(fp, "%3d%10d%10.6f%8.2f\n", t, iter, sqrt(besterr), elapsed);
        start = clock();
        fclose(fp);
    }

    aveiter /= trials;
    avesec /= trials;

    fp = fopen(statsfile, "a");
    fprintf(fp, "\n %d/%d solutions/trials%10.2e iterations/trial%10.2e seconds/trial\n", solcount, trials, aveiter, avesec);
    fclose(fp);

    return 0;
}
