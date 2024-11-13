# CoScheme

An implementation of composable copatterns for Scheme and Racket.

## Directory structure

    .
    ├── racket 
        ├── composable-inline.rkt
            # An implementation that reduces administrative reductions
        ├── composable.rkt
            # Main file containing our Racket implementation
        ├── examples-extend.rkt
            # Examples using the minimal implementation  
        ├── examples.rkt
            # Our paper examples and many more!
        ├── extend.rkt
            # Mininimal implementation with only essential constructs
        ├── test.rkt
            # Examples used to validate the implementation
        └── wordy-examples.rkt
            # A subset of examples.rkt but with a lot of printing
    ├── scheme 
        ├── composable.scm
            # Main file containing our Scheme implementation
        ├── examples.scm
            # Our paper examples and many more!
        └── test.scm
            #  A subset of examples.scm but with a lot of printing
    └── README.md
        # this file

### Tested with:
* Racket 8.14
* Chez Scheme 10.0