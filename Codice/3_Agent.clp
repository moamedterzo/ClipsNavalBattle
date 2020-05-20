;  ---------------------------------------------
;  --- Definizione del modulo e dei template ---
;  ---------------------------------------------
(defmodule AGENT (import MAIN ?ALL) (import ENV ?ALL) (export ?ALL))


(deftemplate g-cell (slot x) (slot y) (slot probability) (slot updated) (slot fired))
(deftemplate g-per-row
	(slot row)
	(slot num)
	(multislot g-cells)
)

(deftemplate g-per-col
	(slot col)
	(slot num)
	(multislot g-cells)
)

;inizializzazione celle 
(defrule initialize-g-cells (declare (salience 30))	
=>
	(loop-for-count (?x 0 9) do
    (loop-for-count (?y 0 9) do
        (assert (g-cell (x ?x) (y ?y) (updated 0) (fired 0) (probability -1)))
		))
)

(defrule initialize-g-row (declare (salience 30))
	(k-per-row (row ?r) (num ?n))
	=>
	(assert (g-per-row (row ?r) (num ?n) (g-cells 0 1 2 3 4 5 6 7 8 9)))
)
(defrule initialize-g-col (declare (salience 30))
	(k-per-col (col ?r) (num ?n))
	=>
	(assert (g-per-col (col ?r) (num ?n) (g-cells 0 1 2 3 4 5 6 7 8 9)))
)

;fine inizializzazione

;regola che scala di uno i candidati quando la probabilità è 0
(defrule manage-water-g-cell (declare (salience 25))
	?gcell <- (g-cell (x ?x) (y ?y) (probability 0))
	?row <- (g-per-row (row ?x) (g-cells $?rows))
	?col <- (g-per-col (col ?y) (g-cells $?cols))
=>
	(printout t "REMOVED cell [" ?x ", " ?y "]" crlf)
	(retract ?gcell)	
	(assert (k-cell (x ?x) (y ?y) (content water)))
	(modify ?row (g-cells (delete-member$ $?rows ?y)))
	(modify ?col (g-cells (delete-member$ $?cols ?x)))
)

;regola che rimuove nell'elenco delle g-cell tutte quelle celle che sono già conosciute 
(defrule initialize-fired-g-cell-boat (declare (salience 25))
	(not (initialized))
	?gcell <- (g-cell (x ?x) (y ?y) (fired 0))
	(k-cell (x ?x) (y ?y) (content ~water))
=>
	(modify ?gcell (fired 1) (probability 1))
)
(defrule stop-remove-g-cell-boat (declare (salience 24))
	(not (initialized))
	=>
	(assert (initialized))
)
;ogni volta che c'è una nuova k-cell, aggiorno la probabilità della g-cell
(defrule sure-k-cell-boat (declare (salience 20))
	(initialized)
	?gcell <- (g-cell (x ?x) (y ?y) (probability ~1))
	(k-cell (x ?x) (y ?y) (content ~water))
=>
	(modify ?gcell (probability 1))
)
;ogni volta che c'è una g-cell sicura, aggiorno il conteggio delle righe e colonne
(defrule update-candidate-g-cell-boat (declare (salience 20))	
	(g-cell (x ?x) (y ?y) (probability 1))
	?row <- (g-per-row (row ?x) (num ?numRow) (g-cells $?rows))
	?col <- (g-per-col (col ?y) (num ?numCol) (g-cells $?cols))
	(test(and (member$ ?y $?rows) (member$ ?x $?cols)))
=>	
	(modify ?row (num (- ?numRow 1)) (g-cells (delete-member$ $?rows ?y)))
	(modify ?col (num (- ?numCol 1)) (g-cells (delete-member$ $?cols ?x)))
)

;le celle che hanno acqua hanno probabilità 0 di avere una nave
(defrule remove-k-cell-water (declare (salience 20))
	?gcell <- (g-cell (x ?x) (y ?y))
	(k-cell (x ?x) (y ?y) (content water))
=>
	(modify ?gcell (probability 0))
)

;celle che hanno righe o colonne vuote (bisogna escludere quelle celle per le quali la probabilità è certa)
(defrule remove-g-cell-col (declare (salience 20))
	(g-per-col (col ?y) (num 0))
	?gcell <- (g-cell (y ?y) (x ?x) (probability ~1))
	=>
	(modify ?gcell (probability 0))
)

(defrule remove-g-cell-row (declare (salience 20))
	(g-per-row (row ?x) (num 0))
	?gcell <- (g-cell (x ?x) (y ?y) (probability ~1))
	=>
	(modify ?gcell (probability 0))
)

;rimozione g-cell per sottomarino
(defrule remove-g-cell-sub (declare (salience 20))
	(k-cell (x ?x) (y ?y) (content sub))
	?gcell <- (g-cell (x ?gx&:(<= (abs(- ?gx ?x)) 1)) (y ?gy&:(<= (abs(- ?gy ?y)) 1)))
	=>
	(modify ?gcell (probability 0))
)
;inferenza sulla presenza di un sottomarino
(defrule inference-k-cell-sub (declare (salience 20))
	(g-cell (x ?x) (y ?y) (probability 1))
	(and (not (g-cell (x ?x) (y ?y2&:(eq 1 (abs (- ?y ?y2))))))
	 	 (not (g-cell (x ?x2&:(eq 1 (abs (- ?x ?x2)))) (y ?y2)))
	)
	=>
	(assert (k-cell (x ?x) (y ?y) (content sub)))
)

;inferenza su top, botton, left, right
;se ho qualcosa sotto ma non ho niente sopra, allora è top
(defrule inference-k-cell-top (declare (salience 20))
	(g-cell (x ?x) (y ?y) (probability 1))
	(g-cell (x ?x2&:(eq ?x2 (+ ?x 1))) (y ?y) (probability 1))
	(not (g-cell (x ?x3&:(eq ?x3 (- ?x 1))) (y ?y)))
	=>
	(assert (k-cell (x ?x) (y ?y) (content top)))
)
(defrule inference-k-cell-bottom (declare (salience 20))
	(g-cell (x ?x) (y ?y) (probability 1))
	(g-cell (x ?x2&:(eq ?x2 (- ?x 1))) (y ?y) (probability 1))
	(not (g-cell (x ?x3&:(eq ?x3 (+ ?x 1))) (y ?y)))
	=>
	(assert (k-cell (x ?x) (y ?y) (content bot)))
)
(defrule inference-k-cell-left (declare (salience 20))
	(g-cell (x ?x) (y ?y) (probability 1))
	(g-cell (y ?y2&:(eq ?y2 (+ ?y 1))) (x ?x) (probability 1))
	(not (g-cell (y ?y3&:(eq ?y3 (- ?y 1))) (x ?x)))
	=>
	(assert (k-cell (x ?x) (y ?y) (content left)))
)
(defrule inference-k-cell-right (declare (salience 20))
	(g-cell (x ?x) (y ?y) (probability 1))
	(g-cell (y ?y2&:(eq ?y2 (- ?y 1))) (x ?x) (probability 1))
	(not (g-cell (y ?y3&:(eq ?y3 (+ ?y 1))) (x ?x)))
	=>
	(assert (k-cell (x ?x) (y ?y) (content right)))
)

;rilevamento dei middle
(defrule inference-k-cell-middle-horizontal (declare (salience 20))
	(g-cell (x ?x) (y ?y) (probability 1))
	(g-cell (y ?y2&:(eq ?y2 (- ?y 1))) (x ?x) (probability 1))
	(g-cell (y ?y3&:(eq ?y3 (+ ?y 1))) (x ?x) (probability 1))
	=>
	(assert (k-cell (x ?x) (y ?y) (content middle)))
)
(defrule inference-k-cell-middle-vertical (declare (salience 20))
	(g-cell (x ?x) (y ?y) (probability 1))
	(g-cell (x ?x2&:(eq ?x2 (- ?x 1))) (y ?y) (probability 1))
	(g-cell (x ?x3&:(eq ?x3 (+ ?x 1))) (y ?y) (probability 1))
	=>
	(assert (k-cell (x ?x) (y ?y) (content middle)))
)

;rimozione e inferenza celle in base al contenuto
(defrule remove-g-cell-top (declare (salience 20))
	(k-cell (x ?x) (y ?y) (content top))
	?gcell <- (g-cell (x ?gx) (y ?gy))
	(or 
		(and (test (eq (- ?x ?gx) 1))
		     (test (eq ?gy ?y))
                )

		(and (test (<= (abs (- ?gx ?x)) 1))
		     (test (eq (abs (- ?gy ?y)) 1))
                )

		(and (test (eq (- ?gx ?x) 2))
		     (test (eq (abs (- ?gy ?y)) 1))
                )
	)
	=>
	(modify ?gcell (probability 0))
)

(defrule inference-g-cell-top (declare (salience 20))
	(k-cell (x ?x) (y ?y) (content top))
	?gcellSure <- (g-cell (x ?x2&:(eq (- ?x2 1) ?x)) (y ?y) (probability ~1))	
	=>
	(modify ?gcellSure (probability 1))
	(printout t "inference [" ?x2 ", " ?y "]" crlf)
)


(defrule remove-g-cell-bottom (declare (salience 20))
	(k-cell (x ?x) (y ?y) (content bot))
	?gcell <- (g-cell (x ?gx) (y ?gy))
	(or 
		(and (test (eq (- ?gx ?x) 1))
		     (test (eq ?gy ?y))
                )

		(and (test (<= (abs (- ?gx ?x)) 1))
		     (test (eq (abs (- ?gy ?y)) 1))
                )

		(and (test (eq (- ?x ?gx) 2))
		     (test (eq (abs (- ?gy ?y)) 1))
                )
	)
	=>
	(modify ?gcell (probability 0))
)

(defrule inference-g-cell-bottom (declare (salience 20))
	(k-cell (x ?x) (y ?y) (content bot))
	?gcellSure <- (g-cell (x ?x2&:(eq (- ?x 1) ?x2)) (y ?y) (probability ~1))	
	=>
	(modify ?gcellSure (probability 1))
	(printout t "inference [" ?x2 ", " ?y "]" crlf)
)


(defrule remove-g-cell-left (declare (salience 20))
	(k-cell (x ?x) (y ?y) (content left))
	?gcell <- (g-cell (x ?gx) (y ?gy))
	(or 
		(and (test (eq (- ?y ?gy) 1))
		     (test (eq ?gx ?x))
                )

		(and (test (<= (abs (- ?gy ?y)) 1))
		     (test (eq (abs (- ?gx ?x)) 1))
                )

		(and (test (eq (- ?gy ?y) 2))
		     (test (eq (abs (- ?gx ?x)) 1))
                )
	)
	=>
	(modify ?gcell (probability 0))
)

(defrule inference-g-cell-left (declare (salience 20))
	(k-cell (x ?x) (y ?y) (content left))
	?gcellSure <- (g-cell (x ?x) (y ?y2&:(eq (- ?y2 1) ?y)) (probability ~1))	
	=>
	(modify ?gcellSure (probability 1))
	(printout t "inference [" ?x ", " ?y2 "]" crlf)
)

(defrule remove-g-cell-right (declare (salience 20))
	(k-cell (x ?x) (y ?y) (content right))
	?gcell <- (g-cell (x ?gx) (y ?gy))
	(or 
		(and (test (eq (- ?gy ?y) 1))
		     (test (eq ?gx ?x))
                )

		(and (test (<= (abs (- ?y ?gy)) 1))
		     (test (eq (abs (- ?gx ?x)) 1))
                )

		(and (test (eq (- ?y ?gy) 2))
		     (test (eq (abs (- ?gx ?x)) 1))
                )
	)
	=>
	(modify ?gcell (probability 0))
)

(defrule inference-g-cell-right (declare (salience 20))
	(k-cell (x ?x) (y ?y) (content right))
	?gcellSure <- (g-cell (x ?x) (y ?y2&:(eq (- ?y 1) ?y2)) (probability ~1))	
	=>
	(modify ?gcellSure (probability 1))
	(printout t "inference [" ?x ", " ?y2 "]" crlf)
)



;regole di inferenza per la cella middle
(defrule g-cell-continue-middle-from-top (declare (salience 20))
 (k-cell (x ?x) (y ?y) (content middle))
 (g-cell (x ?x2&:(eq (- ?x ?x2) 1)) (y ?y) (probability 1))
 ?gcellSure <- (g-cell (x ?x3&:(eq (- ?x3 ?x) 1)) (y ?y) (probability ~1))	
 =>
 (modify ?gcellSure (probability 1))
)

(defrule g-cell-continue-middle-from-bottom (declare (salience 20))
 (k-cell (x ?x) (y ?y) (content middle))
 (g-cell (x ?x2&:(eq (- ?x2 ?x) 1)) (y ?y) (probability 1))
 ?gcellSure <- (g-cell (x ?x3&:(eq (- ?x ?x3) 1)) (y ?y) (probability ~1))	
 =>
 (modify ?gcellSure (probability 1))
)

(defrule g-cell-continue-middle-from-left (declare (salience 20))
 (k-cell (x ?x) (y ?y) (content middle))
 (g-cell (x ?x) (y ?y2&:(eq (- ?y ?y2) 1)) (probability 1))
 ?gcellSure <- (g-cell (x ?x) (y ?y3&:(eq (- ?y3 ?y) 1)) (probability ~1))	
 =>
 (modify ?gcellSure (probability 1))
)

(defrule g-cell-continue-middle-from-right (declare (salience 20))
 (k-cell (x ?x) (y ?y) (content middle))
 (g-cell (x ?x) (y ?y2&:(eq (- ?y2 ?y) 1)) (probability 1))
 ?gcellSure <- (g-cell (x ?x) (y ?y3&:(eq (- ?y ?y3) 1)) (probability ~1))	
 =>
 (modify ?gcellSure (probability 1))
)

;regola di inferenza che rimuove le celle per middle
(defrule remove-g-cell-middle (declare (salience 20))
 (k-cell (x ?x) (y ?y) (content middle))
 ?gcell <- (g-cell (x ?gx&:(eq (abs(- ?gx ?x)) 1)) (y ?gy&:(eq (abs(- ?gy ?y)) 1)))
 =>
   (modify ?gcell (probability 0))
)
;gestione middle quando si inferisce che è verticale
(defrule infer-from-middle-vertical (declare (salience 20))
(k-cell (x ?x) (y ?y) (content middle))
(not (g-cell (y ?yCol&:(eq 1 (abs (- ?y ?yCol)))) (x ?x)))
 ?gcellSure <- (g-cell (x ?x2&:(eq 1 (abs (- ?x ?x2)))) (y ?y)  (probability ~1))
=>
 (modify ?gcellSure (probability 1))
)

(defrule infer-from-middle-horizontal (declare (salience 20))
(k-cell (x ?x) (y ?y) (content middle))
(not (g-cell (x ?xCol&:(eq 1 (abs (- ?x ?xCol)))) (y ?y)))
 ?gcellSure <- (g-cell (y ?y2&:(eq 1 (abs (- ?y ?y2)))) (x ?x)  (probability ~1))
=>
 (modify ?gcellSure (probability 1))
)

; (defrule remove-g-cell-middle-without-row-or-column (declare (salience 20))
;  (k-cell (x ?x) (y ?y) (content middle))
;  ?gcell <- (g-cell (x ?gx) (y ?gy))
;  (or 
; 		(and (test (eq ?y 9))
; 		     (test (eq (- ?y ?gy) 1))
; 			 (test (<= (abs (- ?gx ?x)) 1))
; 		)

; 		(and (test (eq ?y 0))
; 		     (test (eq (- ?gy ?y) 1))
; 			 (test (<= (abs (- ?x ?gx)) 1))
; 		)        

; 		(and (test (eq ?x 9))
; 		     (test (eq (- ?x ?gx) 1))
; 			 (test (<= (abs (- ?gy ?y)) 1))
; 		)

; 		(and (test (eq ?x 0))
; 		     (test (eq (- ?gx ?x) 1))
; 			 (test (<= (abs (- ?y ?gy)) 1))
; 		)
; 	)
;  =>
; (modify ?gcell (probability 0))
; )

;rimozione delle celle escluse dal middle orizzontale
(defrule remove-g-cell-middle-horizontal(declare (salience 20))
 (k-cell (x ?x) (y ?y) (content middle))
 (g-cell (x ?x) (y ?y2&:(eq (abs(- ?y ?y2)) 1)) (probability 1))
 ?gcell <- (g-cell (x ?gx) (y ?gy))
 (and (test (<= (abs(- ?y ?gy)) 1))
	  (test (eq (abs(- ?gx ?x)) 1))
 )
 =>
	(modify ?gcell (probability 0))
)

;rimozione delle celle escluse dal middle verticale
(defrule remove-g-cell-middle-vertical(declare (salience 20))
 (k-cell (x ?x) (y ?y) (content middle))
 (g-cell (x ?x2&:(eq (abs(- ?x ?x2)) 1)) (y ?y) (probability 1))
 ?gcell <- (g-cell (x ?gx) (y ?gy))
 (and (test (<= (abs(- ?x ?gx)) 1))
			 (test (eq (abs(- ?gy ?y)) 1))
 )
 =>
(modify ?gcell (probability 0))
)

;si trovano le celle che si trovano in mezzo ad un top/bottom
(defrule find-g-cell-from-top-bottom (declare (salience 20))
 (k-cell (x ?xTop) (y ?y) (content top))
 (k-cell (x ?xBot&:(<= 3 (- ?xBot ?xTop))) (y ?y) (content bot))
 (g-cell (x ?xMiddle) (y ?y))
 (test (and (> ?xMiddle ?xTop) (< ?xMiddle ?xBot)))
 =>
(assert (k-cell (x ?xMiddle) (y ?y) (content middle)))
)

;si trovano le celle che si trovano in mezzo ad un left/right
(defrule find-g-cell-from-left-right (declare (salience 20))
 (k-cell (y ?yLeft) (x ?x) (content left))
 (k-cell (y ?yRight&:(<= 3 (- ?yRight ?yLeft))) (x ?x) (content right))
 (g-cell (y ?yMiddle) (x ?x))
 (test (and (> ?yMiddle ?yLeft) (< ?yMiddle ?yRight)))
 =>
(assert (k-cell (y ?yMiddle) (x ?x) (content middle)))
)



;;;;;;;;;;;calcolo probabilità
(defrule reset-update-cell-probability (declare (salience 19))
	?gcell <- (g-cell (x ?x) (y ?y) (updated 1) (probability ~1))
	(not (agent-updated))
=>
	(modify ?gcell (updated 0))
)
(defrule no-update-sure-cell-probability (declare (salience 19))
	?gcell <- (g-cell (x ?x) (y ?y) (updated 0) (probability 1))
=>
	(modify ?gcell (updated 1))
)

(defrule set-updated (declare (salience 18))
	(not (agent-updated))
=>
	(assert (agent-updated))
)



;inferenze per quelle righe o colonne che hanno tutti gli elementi contenenti navi
(defrule update-g-cell-probability-row (declare (salience 17))
	(g-per-row (row ?x) (num ?num) (g-cells $?rows))
	(test (eq (length$ $?rows) ?num))
	?gcell <- (g-cell (x ?x) (y ?y) (updated 0))	
=>
	(modify ?gcell (updated 1) (probability 1))
)

(defrule update-g-cell-probability-col (declare (salience 17))
	(g-per-col (col ?y) (num ?num) (g-cells $?cols))
	(test (eq (length$ $?cols) ?num))
	?gcell <- (g-cell (x ?x) (y ?y) (updated 0))	
=>
	(modify ?gcell (updated 1) (probability 1))
)

(defrule update-g-cell-probability (declare (salience 10))
	?gcell <- (g-cell (x ?x) (y ?y) (updated 0))
	(g-per-row (row ?x) (num ?numRow) (g-cells $?rows))
	(g-per-col (col ?y) (num ?numCol) (g-cells $?cols))	
=>
	(bind ?numCellsRow (length$ $?rows))
	(bind ?numCellsCol (length$ $?cols))

	(bind ?probability (/ (+ (/ ?numRow ?numCellsRow) (/ ?numCol ?numCellsCol)) 2))
	(printout t "Probability cell [" ?x ", " ?y "] = " ?probability "." crlf)
	(modify ?gcell (updated 1) (probability ?probability))
)


(defrule fire-best-g-cell
	?upd <- (agent-updated)
	(status (step ?s) (currently running))
	(moves (fires ?mov &:(> ?mov 0)))
	?gcell <- (g-cell (x ?x) (y ?y) (probability ?probability1) (fired 0))
	(not (g-cell (probability ?probability2&:(> ?probability2 ?probability1)) (fired 0)))
	=>		
	(assert (exec (step ?s) (action fire) (x ?x) (y ?y)))
	(modify ?gcell (fired 1))
	(retract ?upd)
	(printout t "Firing [" ?x ", " ?y "]" crlf)
    (pop-focus)
)

(defrule guess-best-g-cell-with-row-or-columns-only-ship
	(status (step ?s)(currently running))
	(moves (fires 0) (guesses ?mov&:(> ?mov 0)))
	?gcell <- (g-cell (x ?x) (y ?y) (fired 0) (probability 1))
	=>
	(modify ?gcell (fired 1))
	(assert (exec (step ?s) (action guess) (x ?x) (y ?y)))
    (printout t "Guessing row-or-columns-only-ship [" ?x ", " ?y "]" crlf)
	(pop-focus)
)

(defrule guess-best-g-cell	
	(status (step ?s)(currently running))
	(moves (fires 0) (guesses ?mov&:(> ?mov 0)))
	?gcell <- (g-cell (x ?x) (y ?y) (probability ?probability1&~1) (fired 0))
	(not (g-cell (probability ?probability2&:(> ?probability2 ?probability1)) (fired 0)))
	=>
	(modify ?gcell (fired 1))
	(assert (exec (step ?s) (action guess) (x ?x) (y ?y)))
    (printout t "Guessing [" ?x ", " ?y "]" crlf)
	(pop-focus)
)

(defrule solve	
	(status (step ?s)(currently running))
	(moves (fires 0) (guesses 0))
	=>
	(assert (exec (step ?s) (action solve)))
    (pop-focus)
)

(defrule solve2 (declare (salience -10))
	(status (step ?s)(currently running))
	(not (g-cell (fired 0)))
	=>
	(assert (exec (step ?s) (action solve)))
    (pop-focus)
)

(defrule print-what-i-know-since-the-beginning 
	(declare (salience -10))
	(k-cell (x ?x) (y ?y) (content ?t) )
=>
	(printout t "I know that cell [" ?x ", " ?y "] contains " ?t "." crlf)
)

