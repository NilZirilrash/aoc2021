; standard functions from my AOC prelude
(define (foldl f x0 lst)
  (if (null? lst)
      x0
      (foldl f (f x0 (car lst)) (cdr lst))))
(define (foldl0 f lst)
  (foldl f (car lst) (cdr lst)))
(define (range start end)
  (if (> start end)
      '()
      (cons start (range (+ start 1) end))))
(define (cartesian-product lst1 lst2)
  (foldl0 append (map (lambda (x1) (map (lambda (x2) (cons x1 x2))
                                        lst2))
                      lst1)))
(define (update-alist-default alist key fn default)
  (cond
    ((null? alist) (list (cons key default)))
    ((equal? key (caar alist)) (cons (cons key (fn (cdar alist)))
                                     (cdr alist)))
    (else (cons (car alist) (update-alist-default (cdr alist) key fn default)))))
(define (count-all lst)
  (let loop ((lst lst)
             (count-list '()))
    (if (null? lst)
        count-list
        (loop (cdr lst)
              (update-alist-default count-list (car lst) (lambda (x) (+ x 1)) 1)))))
(define (times lst n)
  (if (<= n 0)
      '()
      (cons lst (times lst (- n 1)))))

;(load "../lib.scm")

; threading macro because clojure did some things right
(define-syntax (as-> stx)
  (syntax-case stx ()
               ((_ value it) #'value)
               ((_ value it (fn ...) rest ...)
                #'(let ((it value))
                    (as-> (fn ...) it rest ...)))))

(define (vector-foldl fn x0 v)
  (let ((len (vector-length v)))
    (let loop ((i 0)
               (acc x0))
      (if (= i len)
          acc
          (loop (1+ i)
                (fn acc (vector-ref v i)))))))

; move a player with wrap around (i.e., advancing once from position 10
; leaves the player at position 1)
(define (move-player-n player-position n)
  (1+ (modulo (1- (+ player-position n)) 10)))

(define-record-type state (fields pos1 pos2 score1 score2 turn))

; maps state to state. Takes a function with 5 arguments (corresponding to
; the values of the state) and returns five values through (values ... that
; make up the new state, which is constructed by this function
(define (update-state state fn)
  (let ((pos-1 (state-pos1 state))
        (pos-2 (state-pos2 state))
        (score-1 (state-score1 state))
        (score-2 (state-score2 state))
        (turn (state-turn state)))
    (call-with-values (lambda () (fn pos-1 pos-2 score-1 score-2 turn))
                      make-state)))

; state -> something else. Takes a function that takes five arguments
; corresponding to the five values of the state record
(define (state-map fn state)
  (let ((pos-1 (state-pos1 state))
        (pos-2 (state-pos2 state))
        (score-1 (state-score1 state))
        (score-2 (state-score2 state))
        (turn (state-turn state)))
    (fn pos-1 pos-2 score-1 score-2 turn)))

; whether state corresponds to a game state where player 1 has just won
(define (player-1-winning-state? state)
  (state-map (lambda (pos1 pos2 score1 score2 turn)
               (and (>= score1 21) (< score2 21) (= turn 2)))
             state))

; Whether state is the last state in the game. There is redundancy that I have
; left in here
(define (terminal-state? state)
  (or (eqv? 'end state)
      (state-map (lambda (pos1 pos2 score1 score2 turn)
                   (or (>= score1 21) (>= score2 21)))
                 state)))


(define DICE-ROLL-FREQS (count-all
                          (map (lambda (x) (+ (car x) (cadr x) (cddr x)))
                               (cartesian-product (range 1 3)
                                                  (cartesian-product (range 1 3)
                                                                     (range 1 3))))))

; returns pairs of neighbors of the given state alongside the "costs" to get
; there (i.e., the number of ways the dice can combine to get there)
; note that neighbors here is referring to outgoing edges of a particular
; game state
(define (neighbors state)
  (cond
    ; we're at the sink; a sink has no outgoing edges
    ((eqv? state 'end) '())
    ; if the current state is a win for p1, link it to the sink vertex that we
    ; will eventually use to trace all paths back to the source (our starting
    ; state)
    ((player-1-winning-state? state) (list (cons 'end 1)))
    ; if the game ended without player 1 winning
    ((terminal-state? state) '())
    ; if it's player 1's turn
    ((= (state-turn state) 1)
      (map (lambda (roll-and-freq)
             (cons
               (update-state state (lambda (pos1 pos2 score1 score2 turn)
                                     (let ((new-pos1 (move-player-n pos1 (car roll-and-freq))))
                                       (values new-pos1 pos2 (+ score1 new-pos1) score2 2))))
               (cdr roll-and-freq)))
           DICE-ROLL-FREQS))
    (else
       (map (lambda (roll-and-freq)
              (cons
                (update-state state (lambda (pos1 pos2 score1 score2 turn)
                                      (let ((new-pos2 (move-player-n pos2 (car roll-and-freq))))
                                        (values pos1 new-pos2 score1 (+ score2 new-pos2) 1))))
                (cdr roll-and-freq)))
            DICE-ROLL-FREQS))))

;;; here be some dirty dirty code that tries to make handling states
;;; a little more convenient. vectors are more efficient for random access
;;; than linked lists, but a real pain in the tuckus to work with in Scheme

; it's always useful to know how big our state space is
(define NUM-STATES
  (* 10  ; 1 .. 10 number of board spaces for p1
     10  ; 1 .. 10 number of board spaces for p2
     31  ; 0 .. 31 score for p1
     31  ; 0 .. 31 score for p2
     2)) ; two different players

; helper functions to generate an index to a 1D array spanning state space

(define (make-index-coefs d1 . args)
  (if (null? args)
      (list 1)
      (cons (apply * args) (apply make-index-coefs args))))

; the dimensions of each component in our state space
(define STATE-INDEX-DIMS '(10 10 31 31 2))

; multiply these with the corresponding components of our state in order to get
; the 1D index
(define STATE-INDEX-COEFS (vector->immutable-vector
                            (list->vector
                              (apply make-index-coefs STATE-INDEX-DIMS))))
; used for lookup in the reverse direction (translating index back to state)
(define STATE-INDEX-MODULI (cdr STATE-INDEX-DIMS))

(define (state->index state)
  ; recall that we have added another element to our state space to serve as the
  ; sink in our algorithm, so it doesn't fit in our span of state space. So, just
  ; tack it on at N+1
  (if (eqv? state 'end)
      NUM-STATES
      (state-map (lambda (p1 p2 s1 s2 t)
                   (vector-foldl + 0 (vector-map *
                                                 (vector (1- p1) (1- p2) s1 s2 (1- t))
                                                 STATE-INDEX-COEFS)))
             state)))

; much less efficient than state->index, but that's fine, because it's never
; called in tight code. or at all, really. it was useful for debugging
(define (index->state idx)
  (if (= idx NUM-STATES)
      'end
      (let ((raw-values (map (lambda (coeff) (div idx coeff))
                             (vector->list STATE-INDEX-COEFS))))
        (update-state
          (apply make-state (cons (car raw-values)
                                  (map modulo (cdr raw-values) STATE-INDEX-MODULI)))
          (lambda (p1 p2 s1 s2 t)
            (values (1+ p1) (1+ p2) s1 s2 (1+ t)))))))

; Hash tables are terrible in Scheme. Unfortunately, I need something better
; than the O(n) lookup that association lists afford me. Enter association
; vectors, which have O(log(n)) lookup because they're presorted. Horray.
; I'm not saying that I'm proud of this

; Look for the vector index of a cons cell particular key and return it
(define (avec-binary-search v key)
  (let loop ((a 0)
             (b (1- (vector-length v))))
    (if (> a b)
        #f
        (let* ((m (div (+ a b) 2))
               (val (car (vector-ref v m))))
          (cond
            ((= val key) m)
            ((< key val) (loop a (1- m)))
            (else (loop (1+ m) b)))))))

; Mutate the value of a given key using fn
(define (avec-update v key fn)
  (let ((idx (avec-binary-search v key)))
    (vector-set! v idx (cons key (fn (cdr (vector-ref v idx)))))
    v))

; Table lookup of key, returning value
(define (avec-ref v key)
  (let ((idx (avec-binary-search v key)))
    (cdr (vector-ref v idx))))

;;; 220 lines of boilerplate later, it's time for the meat of the problem

; Create a topologically sorted graph out of our states. There is an edge
; between two states if there exists a dice roll for the given player on
; the given turn that transforms the first state into the second.
(define (topologically-sorted-state-graph start)
  ; DFS traversal starting from start, consing on states to the result
  ; as their DFSs complete
  ; Mutation + recursion: a real headache
  (let ((marked (make-vector (1+ NUM-STATES) #f)))
    (let dfs ((cur start)
              (result '())) ; the topologically sorted list of states
      ; if we've already seen the current state vertex
      (if (vector-ref marked (state->index cur))
        result
        (let loop2 ((neighs (map car (neighbors cur))) ; only need the game state, not the edge costs yet
                    (result result))
          (if (null? neighs)
            (begin
              ; we've visited all neighbors; mark the current state as complete
              ; and recurse upwards
              (vector-set! marked (state->index cur) #t)
              (cons cur result))
            ; look at one of the neighbors, DFS it, then continue on with
            ; the other neighbors
            (loop2 (cdr neighs) (dfs (car neighs) result))))))))

; test input: p1: 4, p2: 8
; my input: p1: 6, p2: 10

(define (part-2 player-1 player-2)
  (let* ((initial-state (make-state player-1 player-2 0 0 1))
         (state-graph (topologically-sorted-state-graph initial-state)))
    (display "Finished sorting state graph") (newline)
    ; We work our way backwards along the topologically-sorted set of states,
    ; accumulating the number of paths leading to the sink from the current
    ; state.
    ; Because the states are sorted topologically, we know that we have already
    ; processed all states that follow (i.e., neighboring) the current state, so
    ; we can safely count the number of paths to the end state as the sum of the
    ; number of paths from each neighboring state to the sink
    (let loop ((states (cdr (reverse state-graph))) ; cdr to drop sink vertex 'end
               ; avec contains a mapping from state indices -> number of paths
               ; to that state. Funny story: I originally was trying to key on
               ; the the state records themselves, but it turns out that equal?
               ; doesn't work on records in Chez Scheme. Or rather, it does, but
               ; (equal? (make-state 1 1 0 0 1) (make-state 1 1 0 0 1)) is #f
               ; all states start with number of thereto-leading paths = 0
               ; except the sink, which is initialized as having 1
               (num-ways-to (as-> (map cons (map state->index state-graph)
                                       (times 0 (length state-graph)))
                                  v
                                  (list->vector v)
                                  (avec-update v (state->index 'end) 1+)
                                  ; sort so we can binary search the key
                                  (vector-sort (lambda (a b) (< (car a) (car b))) v))))
      (if (null? states)
          ; assuming we did everything right, our map should tell us how many
          ; ways there are from the starting state to the sink after we process
          ; all states
          (avec-ref num-ways-to (state->index initial-state))
          (let ((cur-state-idx (state->index (car states))))
            (loop
              (cdr states)
              ; do the update
              (avec-update num-ways-to
                           cur-state-idx
                           (lambda (cur-count)
                             (foldl (lambda (acc neigh)
                                      ; recall that neighbors are returned as (neighbor state . count), where
                                      ; count is the number of ways the dice can combine to get to that state
                                      (+ acc (* (cdr neigh) (avec-ref num-ways-to (state->index (car neigh))))))
                                    cur-count
                                    (neighbors (car states)))))))))))

(display (part-2 4 8)) (newline)
