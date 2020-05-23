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
	(multislot gk-cells)
)

(deftemplate g-per-col
	(slot col)
	(slot num)
	(multislot g-cells)
	(multislot gk-cells)
)


(deftemplate g-boat
	(slot size)
	(slot alignment (allowed-values hor ver))
	(slot mainColRow)
	(multislot secColRow)
)

(deftemplate comb-boat
	(slot size)
	(slot alignment (allowed-values hor ver))
	(slot mainColRow)
	(multislot secColRow);contiene tutte le celle tranne quelle per le quali la probabilità è 1
	(multislot initialSecColRow);contiene tutte le celle della combinazione
)



;inizializzazione celle 
(defrule initialize-g-cells (declare (salience 100))	
=>
	(loop-for-count (?x 0 9) do
    (loop-for-count (?y 0 9) do
        (assert (g-cell (x ?x) (y ?y) (updated 0) (fired 0) (probability -1)))
		))
)

(defrule initialize-g-row (declare (salience 100))
	(k-per-row (row ?r) (num ?n))
	=>
	(assert (g-per-row (row ?r) (num ?n) (g-cells 0 1 2 3 4 5 6 7 8 9) (gk-cells 0 1 2 3 4 5 6 7 8 9)))
)
(defrule initialize-g-col (declare (salience 100))
	(k-per-col (col ?r) (num ?n))
	=>
	(assert (g-per-col (col ?r) (num ?n) (g-cells 0 1 2 3 4 5 6 7 8 9) (gk-cells 0 1 2 3 4 5 6 7 8 9)))
)
;fine inizializzazione


;focus inferenze base
(defrule update-status-cells (declare (salience 50))
	(not (agent-updated))
=>
	(focus AGENT_CELL_BASE_INFERENCE)
)


;;;;;;;;;;;calcolo probabilità
(defrule reset-update-cell-probability (declare (salience 12))
	?gcell <- (g-cell (x ?x) (y ?y) (updated 1) (probability ~1))
	(not (agent-updated))
=>
	(modify ?gcell (updated 0))
)

(defrule set-updated (declare (salience 11))
	(not (agent-updated))
=>
	(assert (agent-updated))
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

;condizioni di stop
(defrule solve-no-more-moves
	(status (step ?s)(currently running))
	(moves (fires 0) (guesses 0))
	=>
	(assert (exec (step ?s) (action solve)))
    (pop-focus)
)



;focus sul modulo che effettua le scelte
(defrule make-agent-decision (declare (salience -10))
	(status (step ?s) (currently running))
=>
	(focus AGENT_DECISION)
)






(defrule print-what-i-know-since-the-beginning 
	(declare (salience -10))
	(g-cell (x ?x) (y ?y) (content ?t&~nil) )
=>
	(printout t "I know that cell [" ?x ", " ?y "] contains " ?t "." crlf)
)