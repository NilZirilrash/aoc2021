; chez scheme
; uses fxvectors (fixnum vectors) to increase the speed of indexing

; lib.scm -- some functions from an increasingly growing list of common functions
; used for AOC
(define (foldl f x0 lst)
  (if (null? lst)
      x0
      (foldl f (f x0 (car lst)) (cdr lst))))
(define (foldl0 f lst)
  (foldl f (car lst) (cdr lst)))

(define (read-line)
  (get-line (current-input-port)))

(define (read-all-lines)
  (let ((line (read-line)))
    (if (eof-object? line)
      '()
      (cons line (read-all-lines)))))

(define (repeatedly fn x0 idx)
  (if (<= idx 0)
      x0
      (repeatedly fn (fn x0) (- idx 1))))

(define (range start end)
  (if (> start end)
      '()
      (cons start (range (+ start 1) end))))

(define (cartesian-product lst1 lst2)
  (apply append (map (lambda (x1) (map (lambda (x2) (cons x1 x2))
                                        lst2))
                      lst1)))

;(load "../lib.scm")

; pad the sides of the map with n zeroes
(define (add-border scene n)
  (let ((top-bot (make-list (+ (* 2 n) (fxvector-length (vector-ref scene 0))) 0))
        (left-right (make-list n 0)))
    (list->vector
        (append
          (map (lambda (x) (list->fxvector top-bot)) (make-list n))
          (map (lambda (line) (list->fxvector (append
                                                left-right
                                                (fxvector->list line)
                                                left-right)))
               (vector->list scene))
          (map (lambda (x) (list->fxvector top-bot)) (make-list n))))))

; returns (fxvector look-up table . row-major vector of fxvectors representing the map)
(define (read-input)
  (let* ((lines (read-all-lines))
         (translator (list->fxvector (map (lambda (x) (if (char=? x #\.) 0 1)) (string->list (car lines)))))
         (base-image (vector-map (lambda (line) (list->fxvector
                                                  (map (lambda (x) (if (char=? x #\.) 0 1))
                                                       (string->list line))))
                                 (list->vector (cddr lines)))))
    (cons translator base-image)))

(define ex-input (with-input-from-file "ex.inp" read-input))
(define real-input (with-input-from-file "real.inp" read-input))

(define (display-scene scene)
  (vector-for-each
    (lambda (line)
      (display (list->string (map (lambda (x) (if (zero? x) #\. #\#))
                                  (fxvector->list line))))
      (newline))
    scene))

; calculate whether the new pixel will be on or off
; takes a 1D list of neighbors (TL TM TR ML MM MR BL BM BR)
(define (kernel patch lookup)
  (let ((num (foldl (lambda (acc x) (+ x (* acc 2))) 0 patch)))
    (fxvector-ref lookup num)))

(define (tick scene lookup)
  ; Each point in space behaves identically (according to the same set of rules).
  ; All points in "empty space" (i.e., far from the scene) start as 0 and will stay the
  ; same as each other over time (empty space is homogeneous).
  ; This means that empty space is translationally symmetrical with a 1x1 unit cell.
  ; So, provided that the scene is sufficiently padded with empty space, the entire scene
  ; can be treated as a single periodic unit cell of m x n size (i.e., it wraps around to itself).
  ; The padding behaves like empty space until any changes near the center have the chance to
  ; propagate. Practically, all of this means that I don't need to make any assumptions about
  ; the form of the input; the empty space near the edges still behaves like empty space.
  ;
  ; I've implemented it so point's neighbors wrap around to the other side of the unit cell,
  ; just like how moving off the map to the right in pacman puts him on the left side of the
  ; map.  For example, when considering what value to give the top left point, 
  ; # . . .               # + . +
  ; . . . .  we consider  + + . +
  ; . . . .  the +'s:     . . . .
  ; . . . .               + + . +
  (let* ((len1 (vector-length scene))
         (len2 (fxvector-length (vector-ref scene 0)))
         (new-scene (vector-map (lambda (x) (make-fxvector len2)) (make-vector len1))))
    (let loop ((i 0)
               (j 0))
      (if (= i len1)
        new-scene
        (if (= j len2)
          (loop (1+ i) 0)
          (begin
            ; dirty dirty mutation
            (fxvector-set! (vector-ref new-scene i) j
                           (kernel
                             ; gets the neighbors of the point as a list
                             (map (lambda (coord)
                                    (let ((i (car coord)) (j (cdr coord)))
                                      ; modulo to wrap around to the other side of the unit cell
                                      (fxvector-ref (vector-ref scene (modulo i len1)) (modulo j len2))))
                                  ; all neighbors + current point
                                  (cartesian-product (range (1- i) (1+ i)) (range (1- j) (1+ j))))
                             lookup))
            (loop i (1+ j))))))))

; count the number of lit points
(define (n-lit scene)
  (foldl + 0 (apply append (vector->list (vector-map fxvector->list scene)))))

; (part-2... has a more general implementation
; (define (part-1 input)
;   (let* ((lookup (car input))
;          (scene (add-border (cdr input) 6))
;          (scene1 (tick scene lookup))
;          (scene2 (tick scene1 lookup)))
;     (display-scene scene)
;     (display-scene scene1)
;     (display-scene scene2)
;     (n-lit scene2)))

(define (part-2 input times)
  (let* ((lookup (car input))
         ; I mentioned in (tick... that the scene can be treated as a unit cell as long as it is
         ; "sufficiently padded with empty space" (our boundary condition). In this case, we must
         ; consider how much space is "sufficient." Because each pixel depends on pixels at most
         ; one tile away, changes propagate through space at most one tile per tick. This means
         ; that a point A in empty space cannot be influenced by another point B that is n units
         ; away until n ticks have passed. If all intervening points between A and B are also
         ; empty space, then A is guaranteed to remain empty space for n ticks.
         ; Thus, if we want to maintain our empty-space boundary condition for n ticks, we need
         ; to pad our input image with n tiles of empty space.
         (scene (add-border (cdr input) times))
         (final-scene (repeatedly (lambda (x) (tick x lookup)) scene times)))
    (display-scene final-scene)
    (n-lit final-scene)))
