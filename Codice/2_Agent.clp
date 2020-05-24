;  ---------------------------------------------
;  --- Definizione del modulo e dei template ---
;  ---------------------------------------------
(defmodule AGENT (import MAIN ?ALL) (import ENV ?ALL) (export ?ALL))

;rappresenta la cella per la quale non si cosa cosa potrebbe contenere e con quale probabilità
;tutte le regole di inferenza dell'agente si basano sostanzialmente su questo template
(deftemplate g-cell (slot x) 
					(slot y) 
					(slot probability (default -1)) ;probabilità di contenere una nave
					(slot updated (default 0) (allowed-values 0 1)) ;indica se è stata aggiornata la relativa probabilità
					(slot considered (default 0) (allowed-values 0 1)) ;indica se è una cella da considerare o meno
					(slot content (default nil) (allowed-values water left right middle top bot sub nil)))

;template utilizzato per indicare il numero di elementi ancora da trovare per una riga
(deftemplate g-per-row
	(slot row)
	(slot num)
	(multislot g-cells) ;celle per le quali non si sa se contengono qualcosa o meno
	(multislot gk-cells) ;celle per le quali anche se si conosce il contenuto, non si sa quale barca potrebbe esserci
)

;template simile a quello di sopra, ma utilizzato per le colonne
(deftemplate g-per-col
	(slot col)
	(slot num)
	(multislot g-cells)
	(multislot gk-cells)
)

;template utilizzato per tracciare le navi trovate dall'agente
(deftemplate g-boat
	(slot size (allowed-values 1 2 3 4))
	(slot alignment (allowed-values hor ver)) ;allineamento della nave
	(slot mainColRow) ;se l'allineamento è verticale, indica la colonna, altrimenti indica la riga nella quale la nave si trova
	(multislot secColRow) ;se l'allineamento è verticale, indica le righe nelle quali la nave si trova, altrimenti indica le colonne
)

;rappresenta una possibile disposizione di una nave
;in questa maniera si possono gestire le possibili combinazioni di disposizioni delle navi
(deftemplate comb-boat
	(slot size (allowed-values 1 2 3 4))
	(slot alignment (allowed-values hor ver))
	(slot mainColRow) ;se l'allineamento è verticale, indica la colonna, altrimenti indica la riga nella quale la nave potrebbe trovarsi
	(multislot initialSecColRow) ;se l'allineamento è verticale, indica le righe nelle quali la nave potrebbe trovarsi, altrimenti indica le colonne
	(multislot secColRow); simile a initialSecColRow, ma contiene soltanto le celle per le quali la probabilità di contenere qualcosa è diversa da 1	
)
;;; FINE DEFINIZIONE TEMPLATE ;;;


;;; DEFINIZIONE REGOLE ;;;


;asserzione delle celle 
(defrule initialize-g-cells (declare (salience 100))	
	(not (initialized))
=>
	(loop-for-count (?x 0 9) do
    (loop-for-count (?y 0 9) do
        (assert (g-cell (x ?x) (y ?y)))
		))
)

;sulle celle conosciute a priori non si dovrà fare un'azione di guess o fire
(defrule initial-g-cells-considered (declare (salience 100))	
	(not (initialized))
    ?gcell <- (g-cell (x ?x) (y ?y) (considered 0))
	(k-cell (x ?x) (y ?y))
	=>
	(modify ?gcell (considered 1))
)

;asserzione delle righe a supporto delle inferenze
(defrule initialize-g-row (declare (salience 100))
	(not (initialized))
	(k-per-row (row ?r) (num ?n))
	=>
	(assert (g-per-row (row ?r) (num ?n) 
						(g-cells 0 1 2 3 4 5 6 7 8 9) 
						(gk-cells 0 1 2 3 4 5 6 7 8 9))
			)
)

;asserzione delle colonne a supporto delle inferenze
(defrule initialize-g-col (declare (salience 100))
	(not (initialized))
	(k-per-col (col ?r) (num ?n))
	=>
	(assert (g-per-col (col ?r) (num ?n) 
						(g-cells 0 1 2 3 4 5 6 7 8 9) 
						(gk-cells 0 1 2 3 4 5 6 7 8 9))
						)
)

;termina la fase di inizializzazione
(defrule set-initialized (declare (salience 99))
	(not (initialized))
	=>
	(assert (initialized))
)
;fine inizializzazione


;condizione di stop
(defrule solve-no-more-moves (declare (salience 51))
	(status (step ?s)(currently running))
	(moves (fires 0) (guesses 0))
	=>
	(assert (exec (step ?s) (action solve)))
    (pop-focus)
)

;focus sul modulo che effettua tutte le possibili inferenze
(defrule update-status-cells (declare (salience 50))
	(not (agent-updated))
=>
	(focus AGENT_CELL_BASE_INFERENCE)
)


; regola che permette di aggiornare la probabilità delle celle (solo per quelle celle che non hanno probabilità = 1)
(defrule reset-g-cell-probability (declare (salience 12))
	?gcell <- (g-cell (x ?x) (y ?y) (updated 1) (probability ~1))
	(not (agent-updated))
=>
	(modify ?gcell (updated 0))
)

; regola che permette di passare alla fase di risoluzione
(defrule set-updated (declare (salience 11))
	(not (agent-updated))
=>
	(assert (agent-updated))
)

;calcolo delle probabilità di ciascuna cella di contenere un pezzo della nave
;la probabilità di una cella è data dalla media aritmetica di due fattori
;il numero di celle che potrebbero contenere qualcosa fratto il numero di celle candidate a contenere qualcosa,
;sia per la colonna di riferimento che per la riga di riferimento
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

;focus sul modulo che effettua le scelte di fire o guess
(defrule make-decision
	(status (step ?s) (currently running))
=>
	(focus AGENT_DECISION)
)

;si stampa ciò che un agnete sa sulle celle
(defrule print-what-i-know-since-the-beginning (declare (salience -10))
	(g-cell (x ?x) (y ?y) (content ?t&~nil) )
=>
	(printout t "I know that cell [" ?x ", " ?y "] contains " ?t "." crlf)
)