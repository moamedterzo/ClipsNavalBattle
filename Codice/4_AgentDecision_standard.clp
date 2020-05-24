;  -------------------------------------------------
;  --- Modulo che effettua le azioni dell'agente ---
;  --- Implementazione più prudente              ---
;  -------------------------------------------------
(defmodule AGENT_DECISION (import AGENT ?ALL) (export ?ALL))

; imposta la soglia della probabilità sotto la quale non conviene effettuare una guess per una cella
(defrule set-min-probability (declare (salience 100))
=>
	(assert (min-probability 0.4))
)

;si preferisce effettuare una fire prima su quelle celle per le quali non si conosce il contenuto delle stesse
; in questa maniera è possibile ottenere maggiori informazioni a riguardo
(defrule fire-g-cell-no-content
	?upd <- (agent-updated)
	(status (step ?s) (currently running))
	(moves (fires ?mov &:(> ?mov 0)))
	?gcell <- (g-cell (x ?x) (y ?y) (probability 1) (content nil) (considered 0))
	=>		
	(assert (exec (step ?s) (action fire) (x ?x) (y ?y)))
	(modify ?gcell (considered 1))
	(retract ?upd)
	(printout t "Firing [" ?x ", " ?y "]" crlf)
    (pop-focus)
	(pop-focus)
)

; in alternativa alla regola di sopra, si spara sulla cella che è più probabile abbia qualcosa, senza considerare il contenuto
(defrule fire-g-cell-with-content (declare (salience -1))
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

; si guessano in ordine le celle con maggiore probabilità
(defrule guess-best-g-cell (declare (salience -10))
	(status (step ?s)(currently running))
	(moves (fires 0) (guesses ?mov&:(> ?mov 0)))

	(min-probability ?minProb) ;si ottiene la soglia di probabilità
	?gcell <- (g-cell (x ?x) (y ?y) (probability ?probability1&:(>= ?probability1 ?minProb)) (considered 0))
	(not (g-cell (probability ?probability2&:(> ?probability2 ?probability1)) (considered 0)))
	=>
	(modify ?gcell (considered 1))
	(assert (exec (step ?s) (action guess) (x ?x) (y ?y)))
    (printout t "Guessing [" ?x ", " ?y "]" crlf)
	(pop-focus)
	(pop-focus)
)

;se non ci sono più celle da considerare che hanno una probabilità superiore alla soglia, allora si termina
(defrule solve-no-more-cells
	(status (step ?s)(currently running))

	(min-probability ?minProb)
	(not (g-cell (considered 0) (probability ?prob&:(>= ?prob ?minProb))))
	=>
	(assert (exec (step ?s) (action solve)))
    (pop-focus)
	(pop-focus)
)