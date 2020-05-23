(defmodule AGENT_DECISION (import AGENT ?ALL) (export ?ALL))

;agente 1 (colpisce prima le celle sicure ma che non si conosce il contenuto)
(defrule fire-best-g-cell-greedy
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


;si guessano prima le celle sicure
(defrule action-guess-g-cell-sure (declare (salience -10))
	(status (step ?s)(currently running))
	(moves (fires 0) (guesses ?mov&:(> ?mov 0)))
	?gcell <- (g-cell (x ?x) (y ?y) (fired 0) (probability 1))
	=>
	(modify ?gcell (fired 1))
	(assert (exec (step ?s) (action guess) (x ?x) (y ?y)))
    (printout t "Guessing sure [" ?x ", " ?y "]" crlf)
	(pop-focus)
)

(defrule guess-best-g-cell (declare (salience -11))
	(status (step ?s)(currently running))
	(moves (fires 0) (guesses ?mov&:(> ?mov 0)))
	?gcell <- (g-cell (x ?x) (y ?y) (probability ?probability1&~0) (fired 0))
	(not (g-cell (probability ?probability2&:(> ?probability2 ?probability1)) (fired 0)))
	=>
	(modify ?gcell (fired 1))
	(assert (exec (step ?s) (action guess) (x ?x) (y ?y)))
    (printout t "Guessing unsure [" ?x ", " ?y "]" crlf)
	(pop-focus)
)


(defrule solve-no-more-cells
	(status (step ?s)(currently running))
	(not (g-cell (fired 0) (probability ~0)))
	=>
	(assert (exec (step ?s) (action solve)))
    (pop-focus)
)