;  ---------------------------------------------
;  --- Definizione del modulo e dei template ---
;  ---------------------------------------------
(defmodule AGENT (import MAIN ?ALL) (import ENV ?ALL) (export ?ALL))


(deftemplate g-cell (slot x) (slot y) (slot probability) (slot updated))
(deftemplate g-per-row
	(slot row)
	(slot num)
	(slot g-cells)
)

(deftemplate g-per-col
	(slot col)
	(slot num)
	(slot g-cells)
)

;inizializzazione celle 
(defrule initialize-g-cell (declare (salience 30))
	(not (agent-initialized))
=>
	(assert (initX 0))
	(assert (initY 0))
)

(defrule initialize-g-cell2 (declare (salience 30))
	?xFact <- (initX ?x&:(>= ?x 0)&:(<= ?x 9))
	(initY ?y&:(>= ?y 0)&:(<= ?y 9))
=>
	(assert (g-cell (x ?x) (y ?y) (updated 0) (probability 0)))
	(bind ?newX (+ ?x 1))
	(retract ?xFact)
	(assert (initX ?newX))
)

(defrule initialize-g-cell3 (declare (salience 30))
	?xFact <- (initX 10)
	?yFact <- (initY ?y&:(>= ?y 0)&:(<= ?y 8))
=>
	(bind ?newY (+ ?y 1))
	(retract ?xFact)
	(retract ?yFact)
	(assert (initX 0))
	(assert (initY ?newY))
)

(defrule initialize-g-row (declare (salience 30))
	(not (agent-initialized))
	(k-per-row (row ?r) (num ?n))
	=>
	(assert (g-per-row (row ?r) (num ?n) (g-cells 10)))
)
(defrule initialize-g-col (declare (salience 30))
	(not (agent-initialized))
	(k-per-col (col ?r) (num ?n))
	=>
	(assert (g-per-col (col ?r) (num ?n) (g-cells 10)))
)


(defrule initialize-g-cell4 (declare (salience 29))
	?xFact <- (initX 10)
	?yFact <- (initY 9)
=>
	(retract ?xFact)
	(retract ?yFact)
	(assert (agent-initialized))
)
;fine inizializzazione

;regola che rimuove nell'elenco delle g-cell tutte quelle celle che sono già conosciute 
(defrule remove-k-cell-boat (declare (salience 20))
	?gcell <- (g-cell (x ?x) (y ?y))
	(k-cell (x ?x) (y ?y) (content ~water))
	?row <- (g-per-row (row ?x) (num ?numRow) (g-cells ?numCellsRow))
	?col <- (g-per-col (col ?y) (num ?numCol) (g-cells ?numCellsCol))
=>
	(retract ?gcell)
	(bind ?newNumRow (- ?numRow 1))
	(bind ?newNumCol (- ?numCol 1))
	(bind ?newNumCellsRow (- ?numCellsRow 1))
	(bind ?newNumCellsCol (- ?numCellsCol 1))
	(modify ?row (num ?newNumRow) (g-cells ?newNumCellsRow))
	(modify ?col (num ?newNumCol) (g-cells ?newNumCellsCol))
)

(defrule remove-k-cell-water (declare (salience 20))
	?gcell <- (g-cell (x ?x) (y ?y))
	(k-cell (x ?x) (y ?y) (content water))
	?row <- (g-per-row (row ?x) (g-cells ?numCellsRow))
	?col <- (g-per-col (col ?y) (g-cells ?numCellsCol))
=>
	(retract ?gcell)
	(bind ?newNumCellsRow (- ?numCellsRow 1))
	(bind ?newNumCellsCol (- ?numCellsCol 1))
	(modify ?row (g-cells ?newNumCellsRow))
	(modify ?col (g-cells ?newNumCellsCol))
)

;rimozione delle celle che hanno righe o colonne vuote
(defrule remove-g-cell-col (declare (salience 20))
	(g-per-col (col ?y) (num 0))
	?gcell <- (g-cell (y ?y) (x ?x))
	?row <- (g-per-row (row ?x) (g-cells ?numCellsRow))
	=>
	(retract ?gcell)
	(modify ?row (g-cells (- ?numCellsRow 1)))
)

(defrule remove-g-cell-row (declare (salience 20))
	(g-per-row (row ?x) (num 0))
	?gcell <- (g-cell (x ?x) (y ?y))
	?col <- (g-per-col (col ?y) (g-cells ?numCellsCol))
	=>
	(retract ?gcell)
	(modify ?col (g-cells (- ?numCellsCol 1)))
)

;rimozione g-cell per sottomarino
(defrule remove-g-cell-sub (declare (salience 20))
	(k-cell (x ?x) (y ?y) (content sub))
	?gcell <- (g-cell (x ?gx&:(<= (abs(- ?gx ?x)) 1)) (y ?gy&:(<= (abs(- ?gy ?y)) 1)))
	?row <- (g-per-row (row ?gx) (g-cells ?numCellsRow))
	?col <- (g-per-col (col ?gy) (g-cells ?numCellsCol))
	=>
	(retract ?gcell)
	(bind ?newNumCellsRow (- ?numCellsRow 1))
	(bind ?newNumCellsCol (- ?numCellsCol 1))
	(modify ?row (g-cells ?newNumCellsRow))
	(modify ?col (g-cells ?newNumCellsCol))
)

;rimozione e inferenza celle in base al contenuto
(defrule remove-g-cell-top (declare (salience 20))
	(k-cell (x ?x) (y ?y) (content top))
	?gcell <- (g-cell (x ?gx) (y ?gy))
	?row <- (g-per-row (row ?gx) (g-cells ?numCellsRow))
	?col <- (g-per-col (col ?gy) (g-cells ?numCellsCol))
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
	(printout t "REMOVED [" ?gx ", " ?gy "]" crlf)
	(retract ?gcell)

	(bind ?newNumCellsRow (- ?numCellsRow 1))
	(bind ?newNumCellsCol (- ?numCellsCol 1))
	(modify ?row (g-cells ?newNumCellsRow))
	(modify ?col (g-cells ?newNumCellsCol))
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
	?row <- (g-per-row (row ?gx) (g-cells ?numCellsRow))
	?col <- (g-per-col (col ?gy) (g-cells ?numCellsCol))
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
	(printout t "REMOVED [" ?gx ", " ?gy "]" crlf)
	(retract ?gcell)

	(bind ?newNumCellsRow (- ?numCellsRow 1))
	(bind ?newNumCellsCol (- ?numCellsCol 1))
	(modify ?row (g-cells ?newNumCellsRow))
	(modify ?col (g-cells ?newNumCellsCol))
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
	?row <- (g-per-row (row ?gx) (g-cells ?numCellsRow))
	?col <- (g-per-col (col ?gy) (g-cells ?numCellsCol))
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
	(printout t "REMOVED [" ?gx ", " ?gy "]" crlf)
	(retract ?gcell)

	(bind ?newNumCellsRow (- ?numCellsRow 1))
	(bind ?newNumCellsCol (- ?numCellsCol 1))
	(modify ?row (g-cells ?newNumCellsRow))
	(modify ?col (g-cells ?newNumCellsCol))
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
	?row <- (g-per-row (row ?gx) (g-cells ?numCellsRow))
	?col <- (g-per-col (col ?gy) (g-cells ?numCellsCol))
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
	(printout t "REMOVED [" ?gx ", " ?gy "]" crlf)
	(retract ?gcell)

	(bind ?newNumCellsRow (- ?numCellsRow 1))
	(bind ?newNumCellsCol (- ?numCellsCol 1))
	(modify ?row (g-cells ?newNumCellsRow))
	(modify ?col (g-cells ?newNumCellsCol))
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
 (k-cell (x ?x2&:(eq (- ?x ?x2) 1)) (y ?y) (content ~water))
 ?gcellSure <- (g-cell (x ?x3&:(eq (- ?x3 ?x) 1)) (y ?y) (probability ~1))	
 =>
 (modify ?gcellSure (probability 1))
)

(defrule g-cell-continue-middle-from-bottom (declare (salience 20))
 (k-cell (x ?x) (y ?y) (content middle))
 (k-cell (x ?x2&:(eq (- ?x2 ?x) 1)) (y ?y) (content ~water))
 ?gcellSure <- (g-cell (x ?x3&:(eq (- ?x ?x3) 1)) (y ?y) (probability ~1))	
 =>
 (modify ?gcellSure (probability 1))
)

(defrule g-cell-continue-middle-from-left (declare (salience 20))
 (k-cell (x ?x) (y ?y) (content middle))
 (k-cell (x ?x) (y ?y2&:(eq (- ?y ?y2) 1)) (content ~water))
 ?gcellSure <- (g-cell (x ?x) (y ?y3&:(eq (- ?y3 ?y) 1)) (probability ~1))	
 =>
 (modify ?gcellSure (probability 1))
)

(defrule g-cell-continue-middle-from-right (declare (salience 20))
 (k-cell (x ?x) (y ?y) (content middle))
 (k-cell (x ?x) (y ?y2&:(eq (- ?y2 ?y) 1)) (content ~water))
 ?gcellSure <- (g-cell (x ?x) (y ?y3&:(eq (- ?y ?y3) 1)) (probability ~1))	
 =>
 (modify ?gcellSure (probability 1))
)

;regola di inferenza che rimuove le celle per middle
(defrule remove-g-cell-middle (declare (salience 20))
 (k-cell (x ?x) (y ?y) (content middle))
 ?gcell <- (g-cell (x ?gx&:(eq (abs(- ?gx ?x)) 1)) (y ?gy&:(eq (abs(- ?gy ?y)) 1)))

 ?row <- (g-per-row (row ?gx) (g-cells ?numCellsRow))
 ?col <- (g-per-col (col ?gy) (g-cells ?numCellsCol))

 =>
 (printout t "REMOVED MIDDLE[" ?gx ", " ?gy "]" crlf)
 (retract ?gcell)
 
	(bind ?newNumCellsRow (- ?numCellsRow 1))
	(bind ?newNumCellsCol (- ?numCellsCol 1))
	(modify ?row (g-cells ?newNumCellsRow))
	(modify ?col (g-cells ?newNumCellsCol))
)
;todo gestione middle quando colonne o righe non ci sono
(defrule remove-g-cell-middle-without-row-or-column (declare (salience 20))
 (k-cell (x ?x) (y ?y) (content middle))
 ?gcell <- (g-cell (x ?gx) (y ?gy))
 ?row <- (g-per-row (row ?gx) (g-cells ?numCellsRow))
 ?col <- (g-per-col (col ?gy) (g-cells ?numCellsCol))
 (or 
		(and (test (eq ?y 9))
		     (test (eq (- ?y ?gy) 1))
			 (test (<= (abs (- ?gx ?x)) 1))
		)

		(and (test (eq ?y 0))
		     (test (eq (- ?gy ?y) 1))
			 (test (<= (abs (- ?x ?gx)) 1))
		)        

		(and (test (eq ?x 9))
		     (test (eq (- ?x ?gx) 1))
			 (test (<= (abs (- ?gy ?y)) 1))
		)

		(and (test (eq ?x 0))
		     (test (eq (- ?gx ?x) 1))
			 (test (<= (abs (- ?y ?gy)) 1))
		)
	)
 =>
 (printout t "REMOVED MIDDLE[" ?gx ", " ?gy "]" crlf)
 (retract ?gcell)
 
	(bind ?newNumCellsRow (- ?numCellsRow 1))
	(bind ?newNumCellsCol (- ?numCellsCol 1))
	(modify ?row (g-cells ?newNumCellsRow))
	(modify ?col (g-cells ?newNumCellsCol))
	(modify ?gcell (probability 1))
)

(defrule remove-g-cell-middle-horizontal(declare (salience 20))
 (k-cell (x ?x) (y ?y) (content middle))
 (k-cell (x ?x) (y ?y2&:(eq (abs(- ?y ?y2)) 1)) (content ~water))
 ?gcell <- (g-cell (x ?gx) (y ?gy))
 ?row <- (g-per-row (row ?gx) (g-cells ?numCellsRow))
 ?col <- (g-per-col (col ?gy) (g-cells ?numCellsCol))
 (and (test (<= (abs(- ?y ?gy)) 1))
	  (test (eq (abs(- ?gx ?x)) 1))
 )
 =>
 (printout t "REMOVED MIDDLE [" ?gx ", " ?gy "]" crlf)
 (retract ?gcell)
 
	(bind ?newNumCellsRow (- ?numCellsRow 1))
	(bind ?newNumCellsCol (- ?numCellsCol 1))
	(modify ?row (g-cells ?newNumCellsRow))
	(modify ?col (g-cells ?newNumCellsCol))
	(modify ?gcell (probability 1))
)

(defrule remove-g-cell-middle-vertical(declare (salience 20))
 (k-cell (x ?x) (y ?y) (content middle))
 (k-cell (x ?x2&:(eq (abs(- ?x ?x2)) 1)) (y ?y) (content ~water))
 ?gcell <- (g-cell (x ?gx) (y ?gy))
 ?row <- (g-per-row (row ?gx) (g-cells ?numCellsRow))
 ?col <- (g-per-col (col ?gy) (g-cells ?numCellsCol))
 (and (test (<= (abs(- ?x ?gx)) 1))
			 (test (eq (abs(- ?gy ?y)) 1))
 )
 =>
 (printout t "REMOVED MIDDLE [" ?gx ", " ?gy "]" crlf)
 (retract ?gcell)
 
	(bind ?newNumCellsRow (- ?numCellsRow 1))
	(bind ?newNumCellsCol (- ?numCellsCol 1))
	(modify ?row (g-cells ?newNumCellsRow))
	(modify ?col (g-cells ?newNumCellsCol))
	(modify ?gcell (probability 1))
)

;calcolo probabilità
(defrule reset-update-cell-probability (declare (salience 19))
	?gcell <- (g-cell (x ?x) (y ?y) (updated 1) (probability ~1))
	(not (agent-updated))
=>
	(modify ?gcell (updated 0))
)

(defrule block-update-cell-probability (declare (salience 19))
	?gcell <- (g-cell (x ?x) (y ?y) (probability 1) (updated 0))
	(not (agent-updated))
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
	(g-per-row (row ?x) (num ?num) (g-cells ?num))
	?gcell <- (g-cell (x ?x) (y ?y) (updated 0))	
=>
	(modify ?gcell (updated 1) (probability 1))
)

(defrule update-g-cell-probability-col (declare (salience 17))
	(g-per-col (col ?y) (num ?num) (g-cells ?num))
	?gcell <- (g-cell (x ?x) (y ?y) (updated 0))	
=>
	(modify ?gcell (updated 1) (probability 1))
)

(defrule update-g-cell-probability (declare (salience 17))
	?gcell <- (g-cell (x ?x) (y ?y) (updated 0))
	(g-per-row (row ?x) (num ?numRow) (g-cells ?numCellsRow))
	(g-per-col (col ?y) (num ?numCol) (g-cells ?numCellsCol))
=>
	(bind ?probability (/ (+ (/ ?numRow ?numCellsRow) (/ ?numCol ?numCellsCol)) 2))
	(printout t "Probability cell [" ?x ", " ?y "] = " ?probability "." crlf)
	(modify ?gcell (updated 1) (probability ?probability))
)


(defrule fire-best-g-cell
	?upd <- (agent-updated)
	(status (step ?s) (currently running))
	(moves (fires ?mov &:(> ?mov 0)))
	(g-cell (x ?x) (y ?y) (probability ?probability1))
	(not (g-cell (probability ?probability2&:(> ?probability2 ?probability1))))
	=>		
	(assert (exec (step ?s) (action fire) (x ?x) (y ?y)))
	(retract ?upd)
	(printout t "Firing [" ?x ", " ?y "]" crlf)
    (pop-focus)
)

(defrule guess-best-g-cell-with-row-or-columns-only-ship
	(status (step ?s)(currently running))
	(moves (fires 0) (guesses ?mov&:(> ?mov 0)))
	?gcell <- (g-cell (x ?x) (y ?y) (probability 1))
	=>
	(retract ?gcell)
	(assert (exec (step ?s) (action guess) (x ?x) (y ?y)))
    (printout t "Guessing row-or-columns-only-ship [" ?x ", " ?y "]" crlf)
	(pop-focus)
)

(defrule guess-best-g-cell	
	(status (step ?s)(currently running))
	(moves (fires 0) (guesses ?mov&:(> ?mov 0)))
	?gcell <- (g-cell (x ?x) (y ?y) (probability ?probability1))
	(not (g-cell (probability ?probability2&:(> ?probability2 ?probability1))))
	=>
	(retract ?gcell)
	(assert (exec (step ?s) (action guess) (x ?x) (y ?y)));per la guess andrebbe fatto un calcolo migliore, non va presa la cella piu probabile
															; ma trovata la disposizione piu probabile di navi e restituita (o altro)
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

(defrule print-what-i-know-since-the-beginning 
	(declare (salience -10))
	(k-cell (x ?x) (y ?y) (content ?t) )
=>
	(printout t "I know that cell [" ?x ", " ?y "] contains " ?t "." crlf)
)

