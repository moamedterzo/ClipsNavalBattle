;  ---------------------------------------------
;  --- Definizione del modulo e dei template ---
;  ---------------------------------------------
(defmodule AGENT (import MAIN ?ALL) (import ENV ?ALL) (export ?ALL))

(deftemplate g-cell (slot x) (slot y) (slot probability) 
					(slot updated) (slot fired) (slot content (default nil) (allowed-values water left right middle top bot sub nil)))
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
(defrule initialize-g-cells (declare (salience 20))	
=>
	(loop-for-count (?x 0 9) do
    (loop-for-count (?y 0 9) do
        (assert (g-cell (x ?x) (y ?y) (updated 0) (fired 0) (probability -1)))
		))
)

(defrule initialize-g-row (declare (salience 20))
	(k-per-row (row ?r) (num ?n))
	=>
	(assert (g-per-row (row ?r) (num ?n) (g-cells 0 1 2 3 4 5 6 7 8 9)))
)
(defrule initialize-g-col (declare (salience 20))
	(k-per-col (col ?r) (num ?n))
	=>
	(assert (g-per-col (col ?r) (num ?n) (g-cells 0 1 2 3 4 5 6 7 8 9)))
)

;fine inizializzazione
(defrule update-status-cells (declare (salience 10))
	(not (agent-updated))
=>
	(focus AGENT_CELL_BASE_INFERENCE)
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

(defrule guess-best-g-cell (declare (salience -10))
	(status (step ?s)(currently running))
	(moves (fires 0) (guesses ?mov&:(> ?mov 0)))
	?gcell <- (g-cell (x ?x) (y ?y) (probability ?probability1&~1&~0) (fired 0))
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

(defrule solve2 
	(status (step ?s)(currently running))
	(not (g-cell (fired 0) (probability ~0)))
	=>
	(assert (exec (step ?s) (action solve)))
    (pop-focus)
)


(defrule print-what-i-know-since-the-beginning 
	(declare (salience -10))
	(g-cell (x ?x) (y ?y) (content ?t) )
=>
	(printout t "I know that cell [" ?x ", " ?y "] contains " ?t "." crlf)
)

