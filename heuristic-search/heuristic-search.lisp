;; Copyright 2021 Sony Computer Science Laboratory Paris

;; Licensed under the Apache License, Version 2.0 (the "License");
;; you may not use this file except in compliance with the License.
;; You may obtain a copy of the License at

;;     http://www.apache.org/licenses/LICENSE-2.0

;; Unless required by applicable law or agreed to in writing, software
;; distributed under the License is distributed on an "AS IS" BASIS,
;; WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
;; See the License for the specific language governing permissions and
;; limitations under the License.
;;=========================================================================

(in-package :fcg)

;; This file contains prototype code that was developed for research purposes and should not be used in production environments.
;; No warranties are provided.


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                                 ;;
;; Heuristic search for Fluid Construction Grammar ;;
;;                                                 ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Dedicated Construction Inventory Processor, next-cip-solution and expand-cip-node  ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defclass construction-inventory-processor-heuristic-search (construction-inventory-processor)
  ()
  (:documentation "Construction inventory processor for using heuristic search methods in FCG."))


(defmethod create-construction-inventory-processor ((construction-inventory construction-inventory) (mode (eql :heuristic-search))
                                                    &key initial-cfs direction &allow-other-keys)
  "Create a dedicated construction inventory processor for heuristic search."
  (make-instance 'construction-inventory-processor-heuristic-search
                 :construction-inventory construction-inventory
                 :direction direction
                 :initial-cfs initial-cfs))


(defmethod next-cip-solution ((cip construction-inventory-processor-heuristic-search) &key (notify t))
  "Runs the heuristic construction inventory application search process until
   the next solution is found."
  (when notify (notify cip-started cip))
  (loop with solution = nil
        with search-algorithm = (get-configuration cip :search-algorithm)
        for node = (pop (queue cip))
        when node
        do (unless (cxn-supplier node) ;; node handled the first time
             (setf (cxn-supplier node) 
                   (create-cxn-supplier
                    node (get-configuration cip :cxn-supplier-mode))))
        (when notify (notify cip-next-node node))
       
        (loop for child in (expand-cip-node  ;; make children
                                             node (get-configuration cip :node-expansion-mode))
              ;; node tests
              when (loop for mode in (get-configuration cip :node-tests)
                         always (cip-node-test child mode))
              do (cip-enqueue child cip search-algorithm))

        ;; For meta-layer
        (when (and (get-configuration cip :use-meta-layer)
                   (diagnostics node))
          (multiple-value-bind (new-problems new-fixes)
              (notify-learning node :trigger 'new-node)
            (when new-problems
              (loop for problem in new-problems
                    do (push (type-of problem) (statuses node)))
              (push 'diagnostic-triggered (statuses node)))
             ;; Loop through the new-fixes (they should have a list of construction-application-results in
            ;; their data-field 'fixed-cars), make nodes of them, add them as children, and enqueue them
            ;; Note: fixes don't need to have this field, they may also directly affect the CIP
            (loop for fix in new-fixes ;;
                  when (field? fix 'fixed-cars)
                  do (loop for fixed-car in (get-data fix 'fixed-cars)
                           do
                           (let ((fixed-child (cip-add-child node fixed-car)))
                             (push (type-of (issued-by fix)) (statuses fixed-child))
                             (push 'added-by-repair (statuses fixed-child))
                             (cip-enqueue fixed-child cip search-algorithm))))))
   
        ;; goal tests
        (let ((goal-test-succeeded? (cip-run-goal-tests node cip)))
          (when goal-test-succeeded?
            (setf solution node) ;; node is a solution!
            (when (and (get-configuration cip :use-meta-layer)
                       (get-configuration cip :consolidate-repairs)
                       (repairs node))
              (consolidate-repairs node))) ;; consolidate repairs!
       
          (unless (or (fully-expanded? node) ;;there are other children in the making
                      goal-test-succeeded?) ;;and the node did NOT pass the goal test
            (cip-enqueue node cip search-algorithm))) ;;requeue it so the next children can be explored

        (when notify (notify cip-node-expanded node))
        until (or solution
                  (not (queue cip)))
        finally
        (unless (or solution
                    (succeeded-nodes cip))
          (setf solution (get-last-cip-node cip))
          ;; make-sure goal-tests are run!
          (progn
            (cip-run-goal-tests solution cip)
            (push 'goal-test-failed (statuses solution))))
        (when notify (notify cip-finished solution cip))
        (return (values solution cip))))


(defmethod expand-cip-node ((node cip-node) (mode (eql :full-expansion)))
  "Fully expands cip node at once (with all nodes created by all cxns returned by next-cxn)."
  (loop with nodes-to-queue = nil
        with succeeded-cars = nil
        with failed-cars = nil
        for cxn in (listify (next-cxn (cxn-supplier node) node))
        for new-cars = (multiple-value-list (fcg-apply (safe-cxn cxn (applied-constructions node))
                                                       (car-resulting-cfs (cipn-car node))
                                                       (direction (cip node)) :notify nil
                                                       :configuration (configuration (construction-inventory node))
                                                       :cxn-inventory (construction-inventory node)))
        do
        (setf succeeded-cars (append succeeded-cars (first new-cars)))
        (setf failed-cars (append failed-cars (second new-cars)))
        finally
        (loop for car in succeeded-cars
              do (push (cip-add-child node car) nodes-to-queue))
        (loop for car in failed-cars
              do (cip-add-child node car :cxn-applied nil))
        (setf (fully-expanded? node) t)
        (return nodes-to-queue)))


;;;;;;;;;;;;;;;;;;;;;;;
;; Search algorithms ;;
;;;;;;;;;;;;;;;;;;;;;;;

(defmethod cip-enqueue ((node cip-node) (cip construction-inventory-processor-heuristic-search)
                        (mode (eql :depth-first)))
  "Adds new nodes to the front of the queue (depth-first)."
  (push node (queue cip)))

(defmethod cip-enqueue ((node cip-node) (cip construction-inventory-processor-heuristic-search)
                        (mode (eql :breadth-first)))
  "Adds new nodes to the end of the queue (breadth-first)."
  (setf (queue cip) (append (queue cip) (list node))))

(defmethod cip-enqueue ((node cip-node) (cip construction-inventory-processor-heuristic-search)
                        (mode (eql :best-first)))
  "Adds new nodes to the queue based on their heuristic value (best-first)."
  (if (initial-node-p node)
    (setf (priority node) 1.0)
    (setf (priority node) (heuristic-value node (get-configuration cip :heuristic-value-mode))))
  (setf (queue cip) (sorted-insert (queue cip) node :key #'priority :test #'>)))


(defmethod cip-enqueue ((node cip-node) (cip construction-inventory-processor-heuristic-search)
                        (mode (eql :random)))
  "Randomly inserts the node in the queue."
  (let* ((queue (queue cip))
         (random-position (if queue
                            (random (length queue) #+ccl(make-random-state t))
                            0))
         (first-part (subseq queue 0 random-position))
         (second-part (subseq queue random-position)))
    (setf (queue cip) (append first-part (list node) second-part))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Computing and using heuristics  ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defgeneric heuristic-value (cip-node mode)
  (:documentation "Computes the heuristic value of a cip-node."))

(defmethod heuristic-value ((node cip-node) (mode (eql :sum-heuristics-and-parent)))
  "Heuristic value of a cip-node is the sums of the results of all heuristic functions and the heuristic value of the parent."
  (loop for heuristic in (get-configuration (cip node) :heuristics)
        sum (apply-heuristic node heuristic) into heuristic-value
        finally (return (+ (priority (parent node))
                           heuristic-value))))

(defgeneric apply-heuristic (node mode)
  (:documentation "Applies a single heuristic to a node and returns a score (typically normalized between 0 and 1)."))

(defmethod apply-heuristic ((node cip-node) (mode (eql :nr-of-applied-cxns)))
  "Add 1 for each node."
  1)

(defmethod apply-heuristic ((node cip-node) (mode (eql :nr-of-units-matched)))
  "Returns a normalisation of the number of units matched by the cxn."
  (let ((applied-cxn (get-original-cxn (car-applied-cxn (cipn-car node)))))
    (normalize (length (conditional-part applied-cxn))
               0 10)))


(defmethod apply-heuristic ((node cip-node) (mode (eql :cxn-sets)))
  "Discounts the heuristic value of a node by the distance between the set of the current node and the previous node."
  (let* ((cxn-sets (get-configuration (construction-inventory (cip node))
                                      (if (eq (direction (cip node)) '->)
                                        :production-order :parse-order)))
         (set-of-current (attr-val (first (applied-constructions node)) :label))
         (set-of-previous (if (or (initial-node-p node)
                                  (initial-node-p (parent node)))
                            (first cxn-sets)
                            (attr-val (second (applied-constructions node)) :label))))
    (- (position (symbol-name set-of-previous) cxn-sets :test #'equalp :key #'symbol-name)
       (position (symbol-name set-of-current) cxn-sets :test #'equalp :key #'symbol-name))))


(defmethod apply-heuristic ((node cip-node) (mode (eql :prefer-local-bindings)))
  "Returns a normalisation of the number of words between the matched units (comprehension only)."
  (if (eq (direction (cip node)) '->)
      0.0
      (let* ((match-bindings (car-match-bindings (cipn-car node)))
             (source-ts (left-pole-structure (car-source-cfs (cipn-car node))))
             (sequence-feature-value (cdr (find 'sequence (unit-feature-value (get-root source-ts) 'form) :key #'car)))
             (unit-names-in-bindings
              (remove-duplicates
               (remove nil (mapcar #'(lambda (binding)
                                       (find (cdr binding) sequence-feature-value))
                                   match-bindings)))))
        
        (if (= (length unit-names-in-bindings) 2)                
          (/ 1.0 (float (abs (- (position (first unit-names-in-bindings) sequence-feature-value)
                                (position (second unit-names-in-bindings) sequence-feature-value)))))
          0.0))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Construction suppliers ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; Default: all-cxns ;;
;;;;;;;;;;;;;;;;;;;;;;;

(defclass cxn-supplier ()
  ()
  (:documentation "Construction supplier that returns all
constructions from the construction inventory."))

(defmethod create-cxn-supplier ((node cip-node) (mode (eql :all-cxns)))
  "Makes an instance of cxn-supplier."
  (make-instance 'cxn-supplier))

(defmethod next-cxn ((cxn-supplier cxn-supplier) (node cip-node))
  "Returns all constructions."
  (constructions-for-application (construction-inventory node)))


;; Construction sets ;;
;;;;;;;;;;;;;;;;;;;;;;;

(defclass cxn-supplier-cxn-sets ()
  ((cxn-sets :type list :initform nil :accessor cxn-sets :initarg :cxn-sets
             :documentation "The construction sets."))
  (:documentation "Construction supplier that returns all constructions of the current and remaining sets."))

(defmethod create-cxn-supplier ((node cip-node) (mode (eql :cxn-sets)))
  "Creates an instance of the cxn-supplier and sets the cxn-sets for the applicable direction."
  (make-instance 'cxn-supplier-cxn-sets
                 :cxn-sets (get-configuration (construction-inventory (cip node))
                                              (if (eq (direction (cip node)) '->)
                                                :production-order :parse-order))))

(defmethod next-cxn ((cxn-supplier cxn-supplier-cxn-sets) (node cip-node))
  "Returns all constructions of the current and later sets."
  (if (initial-node-p node)
    (constructions-for-application (construction-inventory node))
    (loop with current-set = (attr-val (first (applied-constructions node)) :label)
          with current-set-index = (position (symbol-name current-set) (cxn-sets cxn-supplier) :test #'equalp :key #'symbol-name)
          with remaining-sets = (subseq (cxn-sets cxn-supplier) current-set-index)
          for construction in (constructions-for-application (construction-inventory node))
          when (member (symbol-name (attr-val construction :label)) remaining-sets :test #'equalp :key #'symbol-name)
          collect construction)))


;; Constructions are hashed ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defclass cxn-supplier-hashed ()
  ()
  (:documentation "Construction supplier that returns all constructions except incompatible hashed ones."))

(defmethod create-cxn-supplier ((node cip-node) (mode (eql :hashed)))
  "Creates an instance of the cxn-supplier."
  (make-instance 'cxn-supplier-hashed))

(defmethod next-cxn ((cxn-supplier cxn-supplier-hashed) (node cip-node))
  "Returns all constructions that satisfy the hash of the node."
  (constructions-for-application-hashed node))


;; Constructions are hashed and divided in sets ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defclass cxn-supplier-cxn-sets-hashed (cxn-supplier-cxn-sets)
  ()
  (:documentation "Construction supplier that combines hashing and construction sets."))

(defmethod create-cxn-supplier ((node cip-node) (mode (eql :cxn-sets-hashed)))
  "Creates an instance of the cxn-supplier and sets the cxn-sets for the applicable direction."
  (make-instance 'cxn-supplier-cxn-sets-hashed
                 :cxn-sets (get-configuration (construction-inventory (cip node))
                                              (if (eq (direction (cip node)) '->)
                                                :production-order :parse-order))))

(defmethod next-cxn ((cxn-supplier cxn-supplier-cxn-sets-hashed) (node cip-node))
  "Returns all constructions that satisfy the hash of the node and are in the current or a later set."
  (if (initial-node-p node)
    (constructions-for-application-hashed node)
    (loop with current-set = (attr-val (first (applied-constructions node)) :label)
          with current-set-index = (position (symbol-name current-set) (cxn-sets cxn-supplier) :test #'equalp :key #'symbol-name)
          with remaining-sets = (subseq (cxn-sets cxn-supplier) current-set-index)
          for construction in (constructions-for-application-hashed node)
          when (member (symbol-name (attr-val construction :label)) remaining-sets :test #'equalp :key #'symbol-name)
          collect construction)))
