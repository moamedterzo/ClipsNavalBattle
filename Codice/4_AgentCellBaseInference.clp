(defmodule AGENT_CELL_BASE_INFERENCE (import AGENT ?ALL))


;regola che scala di uno i candidati quando la probabilità è 0
(defrule manage-water-g-cell (declare (salience 10))
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

;ogni volta che c'è una nuova k-cell, aggiorno la probabilità della g-cell
(defrule initialize-fired-g-cell-boat (declare (salience 10))
	(k-cell (x ?x) (y ?y) (content ?content&~water))
	?gcell <- (g-cell (x ?x) (y ?y) (content nil))
=>
	(modify ?gcell (probability 1) (content ?content))
)


;ogni volta che c'è una g-cell sicura, aggiorno il conteggio delle righe e colonne
(defrule update-candidate-g-cell-boat 
	(g-cell (x ?x) (y ?y) (probability 1))
	?row <- (g-per-row (row ?x) (num ?numRow) (g-cells $?rows))
	?col <- (g-per-col (col ?y) (num ?numCol) (g-cells $?cols))
	(test(and (member$ ?y $?rows) (member$ ?x $?cols)))
=>	
	(modify ?row (num (- ?numRow 1)) (g-cells (delete-member$ $?rows ?y)))
	(modify ?col (num (- ?numCol 1)) (g-cells (delete-member$ $?cols ?x)))
)

;le celle che hanno acqua hanno probabilità 0 di avere una nave
(defrule remove-k-cell-water 
	?gcell <- (g-cell (x ?x) (y ?y))
	(k-cell (x ?x) (y ?y) (content water))
=>
	(modify ?gcell (probability 0))
)

;celle che hanno righe o colonne vuote (bisogna escludere quelle celle per le quali la probabilità è certa)
(defrule remove-g-cell-col 
	(g-per-col (col ?y) (num 0))
	?gcell <- (g-cell (y ?y) (x ?x) (probability ~1))
	=>
	(modify ?gcell (probability 0))
)

(defrule remove-g-cell-row 
	(g-per-row (row ?x) (num 0))
	?gcell <- (g-cell (x ?x) (y ?y) (probability ~1))
	=>
	(modify ?gcell (probability 0))
)

;rimozione g-cell per sottomarino
(defrule remove-g-cell-sub 
	(g-cell (x ?x) (y ?y) (content sub))
	?gcell <- (g-cell (x ?gx&:(<= (abs(- ?gx ?x)) 1)) (y ?gy&:(<= (abs(- ?gy ?y)) 1)))
	=>
	(modify ?gcell (probability 0))
)
;inferenza sulla presenza di un sottomarino
(defrule inference-g-cell-sub 
	?gcell <- (g-cell (x ?x) (y ?y) (probability 1) (content nil))
	(and (not (g-cell (x ?x) (y ?y2&:(eq 1 (abs (- ?y ?y2))))))
	 	 (not (g-cell (x ?x2&:(eq 1 (abs (- ?x ?x2)))) (y ?y2)))
	)
	=>
	(modify ?gcell (content sub))
)

;inferenza su top, botton, left, right
;se ho qualcosa sotto ma non ho niente sopra, allora è top
(defrule inference-g-cell-content-top 
	?gcell <- (g-cell (x ?x) (y ?y) (probability 1) (content nil))
	(g-cell (x ?x2&:(eq ?x2 (+ ?x 1))) (y ?y) (probability 1))
	(not (g-cell (x ?x3&:(eq ?x3 (- ?x 1))) (y ?y)))
	=>
	(modify ?gcell (content top))
)
(defrule inference-g-cell-content-bottom 
	?gcell <- (g-cell (x ?x) (y ?y) (probability 1) (content nil))
	(g-cell (x ?x2&:(eq ?x2 (- ?x 1))) (y ?y) (probability 1))
	(not (g-cell (x ?x3&:(eq ?x3 (+ ?x 1))) (y ?y)))
	=>
	(modify ?gcell (content bot))
)
(defrule inference-g-cell-content-left 
	?gcell <- (g-cell (x ?x) (y ?y) (probability 1) (content nil))
	(g-cell (y ?y2&:(eq ?y2 (+ ?y 1))) (x ?x) (probability 1))
	(not (g-cell (y ?y3&:(eq ?y3 (- ?y 1))) (x ?x)))
	=>
	(modify ?gcell (content left))
)
(defrule inference-g-cell-content-right 
	?gcell <- (g-cell (x ?x) (y ?y) (probability 1) (content nil))
	(g-cell (y ?y2&:(eq ?y2 (- ?y 1))) (x ?x) (probability 1))
	(not (g-cell (y ?y3&:(eq ?y3 (+ ?y 1))) (x ?x)))
	=>
	(modify ?gcell (content right))
)

;rilevamento dei middle
(defrule inference-g-cell-middle-horizontal 
	?gcell <- (g-cell (x ?x) (y ?y) (probability 1) (content nil))
	(g-cell (y ?y2&:(eq ?y2 (- ?y 1))) (x ?x) (probability 1))
	(g-cell (y ?y3&:(eq ?y3 (+ ?y 1))) (x ?x) (probability 1))
	=>
	(modify ?gcell (content middle))
)
(defrule inference-g-cell-middle-vertical 
	?gcell <- (g-cell (x ?x) (y ?y) (probability 1) (content nil))
	(g-cell (x ?x2&:(eq ?x2 (- ?x 1))) (y ?y) (probability 1))
	(g-cell (x ?x3&:(eq ?x3 (+ ?x 1))) (y ?y) (probability 1))
	=>
	(modify ?gcell (content middle))
)

;rimozione e inferenza celle in base al contenuto
(defrule remove-g-cell-top 
	(g-cell (x ?x) (y ?y) (content top))
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

(defrule inference-g-cell-top 
	(g-cell (x ?x) (y ?y) (content top))
	?gcellSure <- (g-cell (x ?x2&:(eq (- ?x2 1) ?x)) (y ?y) (probability ~1))	
	=>
	(modify ?gcellSure (probability 1))
	(printout t "inference [" ?x2 ", " ?y "]" crlf)
)


(defrule remove-g-cell-bottom 
	(g-cell (x ?x) (y ?y) (content bot))
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

(defrule inference-g-cell-bottom
	(g-cell (x ?x) (y ?y) (content bot))
	?gcellSure <- (g-cell (x ?x2&:(eq (- ?x 1) ?x2)) (y ?y) (probability ~1))	
	=>
	(modify ?gcellSure (probability 1))
	(printout t "inference [" ?x2 ", " ?y "]" crlf)
)


(defrule remove-g-cell-left 
	(g-cell (x ?x) (y ?y) (content left))
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

(defrule inference-g-cell-left 
	(g-cell (x ?x) (y ?y) (content left))
	?gcellSure <- (g-cell (x ?x) (y ?y2&:(eq (- ?y2 1) ?y)) (probability ~1))	
	=>
	(modify ?gcellSure (probability 1))
	(printout t "inference [" ?x ", " ?y2 "]" crlf)
)

(defrule remove-g-cell-right
	(g-cell (x ?x) (y ?y) (content right))
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

(defrule inference-g-cell-right 
	(g-cell (x ?x) (y ?y) (content right))
	?gcellSure <- (g-cell (x ?x) (y ?y2&:(eq (- ?y 1) ?y2)) (probability ~1))	
	=>
	(modify ?gcellSure (probability 1))
	(printout t "inference [" ?x ", " ?y2 "]" crlf)
)



;regole di inferenza per la cella middle
(defrule g-cell-continue-middle-from-top 
 (g-cell (x ?x) (y ?y) (content middle))
 (g-cell (x ?x2&:(eq (- ?x ?x2) 1)) (y ?y) (probability 1))
 ?gcellSure <- (g-cell (x ?x3&:(eq (- ?x3 ?x) 1)) (y ?y) (probability ~1))	
 =>
 (modify ?gcellSure (probability 1))
)

(defrule g-cell-continue-middle-from-bottom
 (g-cell (x ?x) (y ?y) (content middle))
 (g-cell (x ?x2&:(eq (- ?x2 ?x) 1)) (y ?y) (probability 1))
 ?gcellSure <- (g-cell (x ?x3&:(eq (- ?x ?x3) 1)) (y ?y) (probability ~1))	
 =>
 (modify ?gcellSure (probability 1))
)

(defrule g-cell-continue-middle-from-left 
 (g-cell (x ?x) (y ?y) (content middle))
 (g-cell (x ?x) (y ?y2&:(eq (- ?y ?y2) 1)) (probability 1))
 ?gcellSure <- (g-cell (x ?x) (y ?y3&:(eq (- ?y3 ?y) 1)) (probability ~1))	
 =>
 (modify ?gcellSure (probability 1))
)

(defrule g-cell-continue-middle-from-right 
 (g-cell (x ?x) (y ?y) (content middle))
 (g-cell (x ?x) (y ?y2&:(eq (- ?y2 ?y) 1)) (probability 1))
 ?gcellSure <- (g-cell (x ?x) (y ?y3&:(eq (- ?y ?y3) 1)) (probability ~1))	
 =>
 (modify ?gcellSure (probability 1))
)

;regola di inferenza che rimuove le celle per middle
(defrule remove-g-cell-middle 
 (g-cell (x ?x) (y ?y) (content middle))
 ?gcell <- (g-cell (x ?gx&:(eq (abs(- ?gx ?x)) 1)) (y ?gy&:(eq (abs(- ?gy ?y)) 1)))
 =>
   (modify ?gcell (probability 0))
)
;gestione middle quando si inferisce che è verticale
(defrule infer-from-middle-vertical 
(g-cell (x ?x) (y ?y) (content middle))
(not (g-cell (y ?yCol&:(eq 1 (abs (- ?y ?yCol)))) (x ?x)))
 ?gcellSure <- (g-cell (x ?x2&:(eq 1 (abs (- ?x ?x2)))) (y ?y)  (probability ~1))
=>
 (modify ?gcellSure (probability 1))
)

(defrule infer-from-middle-horizontal
(g-cell (x ?x) (y ?y) (content middle))
(not (g-cell (x ?xCol&:(eq 1 (abs (- ?x ?xCol)))) (y ?y)))
 ?gcellSure <- (g-cell (y ?y2&:(eq 1 (abs (- ?y ?y2)))) (x ?x)  (probability ~1))
=>
 (modify ?gcellSure (probability 1))
)

;rimozione delle celle escluse dal middle orizzontale
(defrule remove-g-cell-middle-horizontal
 (g-cell (x ?x) (y ?y) (content middle))
 (g-cell (x ?x) (y ?y2&:(eq (abs(- ?y ?y2)) 1)) (probability 1))
 ?gcell <- (g-cell (x ?gx) (y ?gy))
 (and (test (<= (abs(- ?y ?gy)) 1))
	  (test (eq (abs(- ?gx ?x)) 1))
 )
 =>
	(modify ?gcell (probability 0))
)

;rimozione delle celle escluse dal middle verticale
(defrule remove-g-cell-middle-vertical
 (g-cell (x ?x) (y ?y) (content middle))
 (g-cell (x ?x2&:(eq (abs(- ?x ?x2)) 1)) (y ?y) (probability 1))
 ?gcell <- (g-cell (x ?gx) (y ?gy))
 (and (test (<= (abs(- ?x ?gx)) 1))
			 (test (eq (abs(- ?gy ?y)) 1))
 )
 =>
(modify ?gcell (probability 0))
)

;si trovano le celle che si trovano in mezzo ad un top/bottom
(defrule find-g-cell-from-top-bottom 
 (g-cell (x ?xTop) (y ?y) (content top))
 (g-cell (x ?xBot&:(<= 3 (- ?xBot ?xTop))) (y ?y) (content bot))
 ?gcellMiddle <-(g-cell (x ?xMiddle) (y ?y) (content nil))
 (test (and (> ?xMiddle ?xTop) (< ?xMiddle ?xBot)))
 =>
(modify ?gcellMiddle (content middle))
)

;si trovano le celle che si trovano in mezzo ad un left/right
(defrule find-g-cell-from-left-right 
 (g-cell (y ?yLeft) (x ?x) (content left))
 (g-cell (y ?yRight&:(<= 3 (- ?yRight ?yLeft))) (x ?x) (content right))
  ?gcellMiddle <-(g-cell (y ?yMiddle) (x ?x) (content nil))
 (test (and (> ?yMiddle ?yLeft) (< ?yMiddle ?yRight)))
 =>
(modify ?gcellMiddle (content middle))
)


;inferenze per quelle righe o colonne che hanno tutti gli elementi contenenti navi
(defrule update-g-cell-probability-row
	(g-per-row (row ?x) (num ?num) (g-cells $?rows))
	(test (eq (length$ $?rows) ?num))
	?gcell <- (g-cell (x ?x) (y ?y) (updated 0))	
=>
	(modify ?gcell (updated 1) (probability 1))
)

(defrule update-g-cell-probability-col 
	(g-per-col (col ?y) (num ?num) (g-cells $?cols))
	(test (eq (length$ $?cols) ?num))
	?gcell <- (g-cell (x ?x) (y ?y) (updated 0))	
=>
	(modify ?gcell (updated 1) (probability 1))
)



(defrule no-update-sure-cell-probability 
	?gcell <- (g-cell (x ?x) (y ?y) (updated 0) (probability 1))
=>
	(modify ?gcell (updated 1))
)

;;;;;;;;;;;calcolo probabilità
(defrule reset-update-cell-probability (declare (salience -10))
	?gcell <- (g-cell (x ?x) (y ?y) (updated 1) (probability ~1))
	(not (agent-updated))
=>
	(modify ?gcell (updated 0))
)

(defrule set-updated (declare (salience -15))
	(not (agent-updated))
=>
	(assert (agent-updated))
)

(defrule update-g-cell-probability (declare (salience -20))
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


