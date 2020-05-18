;  ---------------------------------------------
;  --- Definizione del modulo e dei template ---
;  ---------------------------------------------
(defmodule AGENT (import MAIN ?ALL) (import ENV ?ALL) (export ?ALL))


(deftemplate g-cell (slot x) (slot y) (slot probability))


(defrule initialize-g-cell (declare (salience 30))
	not (initialized)
	;bisogna asserire tanti fatti quante sono le celle
=>
	(assert (initX 0))
	(assert (initY 0))
)

(defrule initialize-g-cell (declare (salience 30))
	?xFact <- (initX ?x&:(>= ?x 0)&:(<= ?x 9))
	(initY ?y&:(>= ?y 0)&:(<= ?y 9))
=>
	(assert (g-cell (x ?x) (y ?y)))
	(bind ?newX (+ ?x 1))
	(retract ?xFact)
	(assert (initX ?newX)
)

(defrule initialize-g-cell (declare (salience 30))
	?xFact <- (initX 10)
	?yFact <- (initY ?y&:(>= ?y 0)&:(<= ?y 8))
=>
	(bind ?newY (+ ?y 1))
	(retract ?xFact)
	(retract ?yFact)
	(assert (initX 0)
	(assert (initY ?newY)
)

(defrule initialize-g-cell (declare (salience 30))
	?xFact <- (initX 10)
	?yFact <- (initY 9)
=>
	(retract ?xFact)
	(retract ?yFact)
	(assert (initialized))
)

(defrule remove-know-g-cell (declare (salience 20))
	?gcell <- (g-cell (x ?x) (y ?y))
	(k-cell (x ?x) (y ?y))
=>
	(retract(?gcell))
)

(defrule update-g-cell (declare (salience 20))
	(not (updated))
=>;update all g-cell
;usare tutte le inferenze possibili per calcolare la probabilità

	(assert(updated))
)



(defrule fire-best-g-cell	
	(status (step ?s)(currently running))
	(moves (fires ?mov&:(> ?mov 0)))
	(g-cell (x ?x) (y ?y) (probability ?probability1))
	(not (g-cell (probability ?probability2&:(> probability2 probability1))))
	=>		
	(assert (exec (step ?s) (action fire) (x ?x) (y ?y)))
	(retract(updated))
    (pop-focus)
)

(defrule guess-best-g-cell	
	(status (step ?s)(currently running))
	(moves (fire 0) (guesses ?mov&:(> ?mov 0)))
	(g-cell (x ?x) (y ?y) (probability ?probability1))
	(not (g-cell (probability ?probability2&:(> probability2 probability1))))
	=>
	(assert (exec (step ?s) (action guess) (x ?x) (y ?y)));per la guess andrebbe fatto un calcolo migliore, non va presa la cella piu probabile
															; ma trovata la disposizione piu probabile di navi e restituita (o altro)
    (pop-focus)
)




(defrule print-what-i-know-since-the-beginning 
	(declare (salience 10))
	(k-cell (x ?x) (y ?y) (content ?t) )
=>
	(printout t "I know that cell [" ?x ", " ?y "] contains " ?t "." crlf)
)

