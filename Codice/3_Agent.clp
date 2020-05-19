;  ---------------------------------------------
;  --- Definizione del modulo e dei template ---
;  ---------------------------------------------
(defmodule AGENT (import MAIN ?ALL) (import ENV ?ALL) (export ?ALL))


(deftemplate g-cell (slot x) (slot y) (slot probability))
(deftemplate g-per-row
	(slot row)
	(slot num)
)

(deftemplate g-per-col
	(slot col)
	(slot num)
)

(defrule initialize-g-cell (declare (salience 30))
	(not (agent-initialized))
	;bisogna asserire tanti fatti quante sono le celle
=>
	(assert (initX 0))
	(assert (initY 0))
)

(defrule initialize-g-cell2 (declare (salience 30))
	?xFact <- (initX ?x&:(>= ?x 0)&:(<= ?x 9))
	(initY ?y&:(>= ?y 0)&:(<= ?y 9))
=>
	(assert (g-cell (x ?x) (y ?y) (probability 0.1)))
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
	(assert (g-per-row (row ?r) (num ?n)))
)
(defrule initialize-g-col (declare (salience 30))
	(not (agent-initialized))
	(k-per-col (col ?r) (num ?n))
	=>
	(assert (g-per-col (col ?r) (num ?n)))
)


(defrule initialize-g-cell4 (declare (salience 29))
	?xFact <- (initX 10)
	?yFact <- (initY 9)
=>
	(retract ?xFact)
	(retract ?yFact)
	(assert (agent-initialized))
)

(defrule remove-know-g-cell (declare (salience 20))
	?gcell <- (g-cell (x ?x) (y ?y))
	(k-cell (x ?x) (y ?y))
	?row <- (g-per-row (row ?x) (num ?numRow))
	?col <- (g-per-col (col ?y) (num ?numCol))
=>
	(retract ?gcell)
	(bind ?newNumRow (- ?numRow 1))
	(bind ?newNumCol (- ?numCol 1))
	(modify ?row (num ?newNumRow))
	(modify ?col (num ?newNumCol))
)

(defrule remove-g-cell-col (declare (salience 20))
	(g-per-col (col ?y) (num 0))
	?gcell <- (g-cell (y ?y))
	=>
	(retract ?gcell)
)

(defrule remove-g-cell-row (declare (salience 20))
	(g-per-row (row ?x) (num 0))
	?gcell <- (g-cell (x ?x))
	=>
	(retract ?gcell)
)

(defrule remove-g-cell-sub (declare (salience 20))
	(k-cell (x ?x) (y ?y) (content sub))
	?gcell <- (g-cell (x ?gx&:(<= (abs(- ?gx ?x)) 1)) (y ?gy&:(<= (abs(- ?gy ?y)) 1)))
	=>
	(retract ?gcell)
)

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
	(printout t "REMOVED [" ?gx ", " ?gy "]" crlf)
	(retract ?gcell)
)

(defrule inference-g-cell-top (declare (salience 20))
	(k-cell (x ?x) (y ?y) (content top))
	?gcellSure <- (g-cell (x ?x2&:(eq (- ?x2 1) ?x)) (y ?y) (probability ~1))	
	=>
	(modify ?gcellSure (probability 1))
	(printout t "inference [" ?x2 ", " ?y "]" crlf)
)



(defrule update-g-cell (declare (salience 19))
	(not (updated))
=>;update all g-cell
;usare tutte le inferenze possibili per calcolare la probabilità

	(assert (updated))
)



(defrule fire-best-g-cell
	?upd <- (updated)
	(status (step ?s) (currently running))
	(moves (fires ?mov &:(> ?mov 0)))
	(g-cell (x ?x) (y ?y) (probability ?probability1))
	(not (g-cell (probability ?probability2&:(> ?probability2 ?probability1))))
	=>		
	(assert (exec (step ?s) (action fire) (x ?x) (y ?y)))
	(retract ?upd)
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

