# Logical Grammar Embedding

This is the repository for "A logical word embedding for learning grammar" (http://arxiv.org/abs/2304.14590), a manuscript detailing the logical grammar embedding (LGE). LGE is a system for encoding syntactic structure in natural language in the form of binary codes for each word, in such a way that the codes can be interpreted as elements of a quasigroup. It is inspired by the logical structure of pregroup grammars and categorial grammars.

`parse.c` is the code (written in C) for parsing a set of sentences. Compile it with `gcc -O2 parse.c -lm -o parse`. To use modified versions of the algorithm --- the ones described in the manuscript include allowing for homographs, allowing bit flips, allowing multiple base types per node --- you can change the settings of the parameters `nwc`, `bitflip`, `multibase`, etc. at the beginning of the code and recompile. `parse` expects seven arguments:
- the name of the text file containing the training sentences
- the number of sentences to use from that text file
- the name of a "seed" file (if you have some codes that you would like certain words to have); the format should follow the example of the file named `seed`; to not use any seed you can type `no` or `none` or anything other than a valid file name
- the number of iterations to execute; it usually takes several thousand to find good parses
- the number of trials to run
- the desired name for results files

`declarative.txt` is a set of simple declarative training sentences for testing out the parse algorithm. `fic.txt` is a set of sentences (declarative, imperative, interrogative, fragments, etc.) from works of fiction, sampled from the Corpus of Contemporary American English (https://www.english-corpora.org/coca/).

An example command (after compiling): `./parse declarative.txt 100 none 3 .5 10000 10 .000001 10 test`

Once you have parsed some setences, you can use `generate.ipynb` to generate novel sentences from the inferred grammar.
