;  -------------------------------------------------
;  --- Modulo che effettua le azioni dell'agente ---
;  --- Implementazione più rischiosa             ---
;  -------------------------------------------------
(defmodule AGENT_DECISION (import AGENT ?ALL) (export ?ALL))

; si spara sulla cella che è più probabile abbia qualcosa
(defrule fire-best-g-cell
	?upd <- (agent-updated)
	(status (step ?s) (currently running))
	(moves (fires ?mov &:(> ?mov 0)))
	?gcell <- (g-cell (x ?x) (y ?y) (probability ?probability1) (considered 0))
	(not (g-cell (probability ?probability2&:(> ?probability2 ?probability1)) (considered 0)))
	=>		
	(assert (exec (step ?s) (action fire) (x ?x) (y ?y)))
	(modify ?gcell (considered 1))
	(retract ?upd)
	(printout t "Firing [" ?x ", " ?y "]" crlf)
    (pop-focus)
	(pop-focus)
)

;si guessano prima le celle sicure
(defrule guess-best-g-cell (declare (salience -10))
	(status (step ?s)(currently running))
	(moves (fires 0) (guesses ?mov&:(> ?mov 0)))

	?gcell <- (g-cell (x ?x) (y ?y) (probability ?probability1) (considered 0))
	(not (g-cell (probability ?probability2&:(> ?probability2 ?probability1)) (considered 0)))
	=>
	(modify ?gcell (considered 1))
	(assert (exec (step ?s) (action guess) (x ?x) (y ?y)))
    (printout t "Guessing [" ?x ", " ?y "]" crlf)
	(pop-focus)
	(pop-focus)
)

;se non ci sono più celle da considerare che hanno una probabilità superiore a zero, allora si termina
(defrule solve-no-more-cells
	(status (step ?s)(currently running))
	(not (g-cell (considered 0) (probability ~0)))
	=>
	(assert (exec (step ?s) (action solve)))
    (pop-focus)
	(pop-focus)
)