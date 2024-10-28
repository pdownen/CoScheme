#!r6rs
(import (rnrs))
;;  (library-directories (cons "/home/adrianoii/repositories/CoScheme/scheme" (library-directories)))
(library-directories (cons "../../scheme/" (cons "scheme" (library-directories))))
(import (compose))

(define l1 '(leaf 42))
(define t0 '(node (leaf 1) 2 (leaf 3)))
(define t1 '(node (node (leaf 1) 2 (leaf 3)) 4 (leaf 5)))

;; Tree :: a + (Tree a * a * Tree a) 
;; search : Tree a -> [a]
(define*
  [((search ('leaf e)) 'dfs) = (list e)]
  [((search ('node l e r)) 'dfs) = (append ((search l) 'dfs) (list e) ((search r) 'dfs))]
  
)


((search l1) 'dfs)
((search t0) 'dfs)
((search t1) 'dfs)