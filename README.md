# Logical Grammar Embedding

This is the repository for "A logical word embedding for learning grammar" (http://arxiv.org/abs/2304.14590), a manuscript detailing the logical grammar embedding (LGE). LGE is a system for encoding syntactic structure in natural language in the form of binary codes for each word, in such a way that the codes can be interpreted as elements of a quiasigroup. It is inspired the logical structure of pregroup grammars and categorial grammars.

`parse.c` is the code (written in C) for parsing a set of sentences. `declarative.txt` is a set of training sentences for testing out the parse algorithm.

`generate.ipynb` is a Python notebook for taking a parse and using it to generate novel sentences.
