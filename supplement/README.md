# CoScheme

An implementation of composable copatterns for Scheme and Racket.

## Directory structure

    .
    ├── racket 
	    # Macro implementation of copatterns in Racket
        ├── composable.rkt
            # Main file containing our Racket implementation
        ├── examples.rkt
            # Our paper examples and many more!
        └── test.rkt
            # Examples used to validate the implementation
    ├── scheme 
	    # Macro implementation of copatterns in standard R6RS Scheme
        ├── composable.scm
            # Main file containing our Scheme implementation
        ├── examples.scm
            # Our paper examples and many more!
        └── test.scm
            # Examples used to validate the implementation
    ├── appendix.pdf
		# appendix with proofs showing calculations of the main theorems
    └── README.md
        # this file

### Tested with:
* Racket 8.14
* Chez Scheme 10.0
