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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                                                            ;;
;; Demonstration of heuristic search strategies in Fluid Construction Grammar ;;
;;                                                                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This file contains prototype code that was developed for research purposes and should not be used in production environments.
;; No warranties are provided.

;; Loading ... ;;
;;;;;;;;;;;;;;;;;

(ql:quickload :fcg)
(in-package :fcg)

(activate-monitor trace-fcg)
(load "<path-to-heuristic-search-file>")

;; Search algorithms and heuristics ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(def-fcg-constructions example-grammar
  :fcg-configurations (;; to activate heuristic search
                       (:construction-inventory-processor-mode . :heuristic-search) ;; use dedicated cip
                       (:node-expansion-mode . :full-expansion) ;; always fully expands node immediately
                       (:cxn-supplier-mode . :all-cxns) ;; returns all cxns at once
                       ;; for using heuristics
                       (:search-algorithm . :best-first) ;; :depth-first, :breadth-first :random
                       (:heuristics :nr-of-applied-cxns :nr-of-units-matched) ;; list of heuristic functions (modes of #'apply-heuristic) - only used with best-first search
                       (:heuristic-value-mode . :sum-heuristics-and-parent) ;; how to use results of heuristic functions for scoring a node
                       ;; cxn sets
                       (:parse-order lex phrasal transitive intransitive)
                       (:production-order lex phrasal transitive intransitive)
                       ;; goal tests
                       (:parse-goal-tests :no-applicable-cxns :connected-semantic-network)
                       (:production-goal-tests :no-applicable-cxns :no-meaning-in-root))

  ;; Lexical constructions
  (def-fcg-cxn the-cxn
               ((?the-word
                 (args (?x))
                 (sem-cat (sem-class referent))
                 (syn-cat (lex-class article)))
                <-
                (?the-word
                 (HASH meaning ((activate-referent ?x)))                     
                 --
                 (HASH form ((string ?the-word  "the")))))
               :cxn-set lex)

  (def-fcg-cxn a-cxn
               ((?a-word
                 (args (?i))
                 (sem-cat (sem-class referent))
                 (syn-cat (lex-class article)))
                <-
                (?a-word
                 (HASH meaning ((introduce-referent ?i)))                     
                 --
                 (HASH form ((string ?a-word "a")))))
               :cxn-set lex)

  (def-fcg-cxn mouse-cxn
               ((?mouse-word
                 (args (?m))
                 (sem-cat (sem-class physical-entity))
                 (syn-cat (lex-class noun)
                          (head ?head))
                 (boundaries ((leftmost-unit ?mouse-word)
                              (rightmost-unit ?mouse-word))))
                <-
                (?mouse-word
                 (HASH meaning ((mouse ?m)))                     
                 --
                 (HASH form ((string ?mouse-word  "mouse")))))
               :cxn-set lex)

  (def-fcg-cxn green-cxn
               ((?green-word
                 (args (?g))
                 (sem-cat (sem-class property))
                 (syn-cat (lex-class adjective)))
                <-
                (?green-word
                 (HASH meaning ((green ?g)))                     
                 --
                 (HASH form ((string ?green-word  "green")))))
               :cxn-set lex)
  
  (def-fcg-cxn eats-cxn
               ((?eats-word
                 (args (?c))
                 (sem-cat (sem-class relation))
                 (syn-cat (lex-class verb)
                          (type ?type)))
                <-
                (?eats-word
                 (HASH meaning ((consume ?c)))                     
                 --
                 (HASH form ((string ?eats-word  "eats")))))
               :cxn-set lex)

  (def-fcg-cxn chases-cxn
               ((?chases-word
                 (args (?c))
                 (sem-cat (sem-class relation))
                 (syn-cat (lex-class verb)
                          (type ?type)))
                <-
                (?chases-word
                 (HASH meaning ((chase ?c)))                     
                 --
                 (HASH form ((string ?chases-word  "chases")))))
               :cxn-set lex)
  
  (def-fcg-cxn cat-cxn
               ((?cat-word
                 (args (?c))
                 (sem-cat (sem-class physical-entity))
                 (syn-cat (lex-class noun)
                          (head ?head))
                 (boundaries ((leftmost-unit ?cat-word)
                              (rightmost-unit ?cat-word))))
                <-
                (?cat-word
                 (HASH meaning ((cat ?c)))                     
                 --
                 (HASH form ((string ?cat-word  "cat")))))
               :cxn-set lex)
  
  ;;Grammatical Constructions
  ;; NP -> ART NOUN
  (def-fcg-cxn article-noun-cxn
               ((?noun-phrase
                 (args (?x))
                 (sem-cat (sem-function referring-expression))
                 (syn-cat (phrase-type noun-phrase))
                 (subunits (?article ?noun))
                 (boundaries ((leftmost-unit ?article)
                              (rightmost-unit ?noun))))
                <-
                (?article
                 (args (?x))
                 (sem-cat (sem-class referent))
                 --
                 (syn-cat (lex-class article)))
                (?noun
                 (args (?x))
                 (sem-cat (sem-class physical-entity))                   
                 --
                 (syn-cat (lex-class noun)
                          (head ?noun-phrase)))
                (?noun-phrase
                 --
                 (HASH form ((precedes ?article ?noun)))))
               :cxn-set phrasal)

  (def-fcg-cxn adjective-noun-cxn
               ((?noun-phrase
                 (args (?x))
                 (sem-cat (sem-function referring-expression))
                 (syn-cat (phrase-type noun-phrase))
                 (subunits (?adjective ?noun))
                 (boundaries ((leftmost-unit ?adjective)
                              (rightmost-unit ?rightmost-noun))))
                <-
                (?adjective
                 (args (?x))
                 (sem-cat (sem-class property))
                 --
                 (syn-cat (lex-class adjective)))
                (?noun
                 (args (?x))
                 (sem-cat (sem-class physical-entity))                   
                 --
                 (syn-cat (lex-class noun)
                          (head ?noun-phrase))
                 (boundaries ((leftmost-unit ?leftmost-noun)
                              (rightmost-unit ?rightmost-noun))))
                (?noun-phrase
                 --
                 (HASH form ((precedes ?adjective ?rightmost-noun)))))
               :cxn-set phrasal)

  
  
  ;; VP -> V
  (def-fcg-cxn verb-phrase-cxn
               ((?verb-phrase
                 (args ?args)
                 (sem-cat (sem-function relational-expression))
                 (syn-cat (phrase-type verb-phrase)
                          (type ?type))
                 (subunits (?verb))
                 (boundaries ((leftmost-unit ?verb)
                             (rightmost-unit ?verb))))
                <-
                (?verb
                 (args ?args)
                 (sem-cat (sem-class relation))
                 --
                 (syn-cat (lex-class verb)
                          (type ?type))))
               :cxn-set phrasal)
  
  ;; Transitive-clause -> NP VP NP
  (def-fcg-cxn transitive-clause-cxn
               ((?transitive-clause
                 (args (?x ?y))
                 (sem-cat (sem-class predicating-expression))
                 (syn-cat (lex-class transitive-clause))
                 (subunits (?subject-noun-phrase ?verb-phrase ?object-noun-phrase)))
                <-
                (?subject-noun-phrase
                 (args (?x))
                 (sem-cat (sem-function referring-expression))
                 --
                 (syn-cat (phrase-type noun-phrase))
                 (boundaries ((rightmost-unit ?rightmost-subject-unit))))
                (?verb-phrase
                 (args (?ev))
                 (sem-cat (sem-function relational-expression))
                 --
                 (syn-cat (phrase-type verb-phrase)
                          (type transitive))
                 (boundaries ((leftmost-unit ?leftmost-verb-unit)
                              (rightmost-unit ?rightmost-verb-unit))))
                (?object-noun-phrase
                 (args (?y))
                 (sem-cat (sem-function referring-expression))
                 --
                 (syn-cat (phrase-type noun-phrase))
                 (boundaries ((leftmost-unit ?leftmost-object-unit))))
                (?transitive-clause
                 (HASH meaning ((:arg0 ?ev ?x)
                                (:arg1 ?ev ?y)))
                 --
                 (HASH form ((meets ?rightmost-subject-unit ?leftmost-verb-unit)
                             (meets ?rightmost-verb-unit ?leftmost-object-unit)))))
               :cxn-set transitive)

  (def-fcg-cxn intransitive-clause-cxn
               ((?intransitive-clause
                 (args (?x ?y))
                 (sem-cat (sem-class predicating-expression))
                 (syn-cat (lex-class intransitive-clause))
                 (subunits (?subject-noun-phrase ?verb-phrase)))
                <-
                (?subject-noun-phrase
                 (args (?x))
                 (sem-cat (sem-function referring-expression))
                 --
                 (syn-cat (phrase-type noun-phrase))
                 (boundaries ((rightmost-unit ?rightmost-subject-unit))))
                (?verb-phrase
                 (args (?ev))
                 (sem-cat (sem-function relational-expression))
                 --
                 (syn-cat (phrase-type verb-phrase)
                          (type intransitive))
                 (boundaries ((leftmost-unit ?leftmost-verb-unit))))
                (?intransitive-clause
                 (HASH meaning ((:arg0 ?ev ?x)))
                 --
                 (HASH form ((meets ?rightmost-subject-unit ?leftmost-verb-unit)))))
               :cxn-set intransitive))


;; Search algorithm: depth-first:
(set-configuration *fcg-constructions* :search-algorithm :depth-first)
(comprehend-and-formulate "the cat eats the mouse")


;; Search algorithm: breadth-first:
(set-configuration *fcg-constructions* :search-algorithm :breadth-first)
(comprehend-and-formulate "the cat eats the mouse")


;; Search algorithm: random:
(set-configuration *fcg-constructions* :search-algorithm :random)
(comprehend-and-formulate "the cat eats the mouse")

;; Search algorithm: best-first:
(progn
  (set-configuration *fcg-constructions* :search-algorithm :best-first)
  (set-configuration *fcg-constructions* :heuristics '(:nr-of-applied-cxns :nr-of-units-matched))
  (set-configuration *fcg-constructions* :heuristic-value-mode :sum-heuristics-and-parent))

(comprehend-and-formulate "the cat eats the mouse")

;; Construction sets:
(progn
  (set-configuration *fcg-constructions* :search-algorithm :best-first)
  (set-configuration *fcg-constructions* :cxn-supplier-mode :cxn-sets)
  (set-configuration *fcg-constructions* :heuristics '(:nr-of-applied-cxns :cxn-sets)))

(comprehend-and-formulate "the cat eats the mouse ")

;; Prefer local bindings:
(progn
  (set-configuration *fcg-constructions* :search-algorithm :best-first)
  (set-configuration *fcg-constructions* :cxn-supplier-mode :cxn-sets)
  (set-configuration *fcg-constructions* :heuristics '(:nr-of-applied-cxns :prefer-local-bindings :cxn-sets)))
(comprehend "the cat chases a green mouse")


;; Using a hashed construction set ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-fcg-constructions example-grammar-hashed
  :fcg-configurations (;; to activate heuristic search
                       (:construction-inventory-processor-mode . :heuristic-search) ;; use dedicated cip
                       (:node-expansion-mode . :full-expansion) ;; always fully expands node immediately
                       (:cxn-supplier-mode . :hashed) ;; use hashing
                       ;; for using heuristics
                       (:search-algorithm . :best-first) ;; :depth-first, :breadth-first
                       (:heuristics :nr-of-applied-cxns :nr-of-units-matched) ;; list of heuristic functions (modes of #'apply-heuristic)
                       (:heuristic-value-mode . :sum-heuristics-and-parent) ;; how to use results of heuristic functions for scoring a node
                       ;; cxn sets
                       (:parse-order lex phrasal transitive intransitive)
                       (:production-order lex phrasal transitive intransitive)
                       ;; goal tests
                       (:parse-goal-tests :no-applicable-cxns :connected-semantic-network)
                       (:production-goal-tests :no-applicable-cxns :no-meaning-in-root))

  :hashed t
  ;; Lexical constructions
  (def-fcg-cxn the-cxn
               ((?the-word
                 (args (?x))
                 (sem-cat (sem-class referent))
                 (syn-cat (lex-class article)))
                <-
                (?the-word
                 (HASH meaning ((unique ?x)))                     
                 --
                 (HASH form ((string ?the-word  "the")))))
               :cxn-set lex
               :attributes (:string "the" :meaning unique))

  (def-fcg-cxn mouse-cxn
               ((?mouse-word
                 (args (?x))
                 (sem-cat (sem-class physical-entity))
                 (syn-cat (lex-class noun)))
                <-
                (?mouse-word
                 (HASH meaning ((mouse ?x)))                     
                 --
                 (HASH form ((string ?mouse-word  "mouse")))))
               :cxn-set lex
               :attributes (:string "mouse" :meaning mouse))
  
  (def-fcg-cxn eats-cxn
               ((?eats-word
                 (args (?c))
                 (sem-cat (sem-class relation))
                 (syn-cat (lex-class verb)
                          (type ?type)))
                <-
                (?eats-word
                 (HASH meaning ((consume ?c)))                     
                 --
                 (HASH form ((string ?eats-word  "eats")))))
               :cxn-set lex
               :attributes (:string "eats" :meaning consume))
  
  (def-fcg-cxn cat-cxn
               ((?cat-word
                 (args (?x))
                 (sem-cat (sem-class physical-entity))
                 (syn-cat (lex-class noun)))
                <-
                (?cat-word
                 (HASH meaning ((cat ?x)))                     
                 --
                 (HASH form ((string ?cat-word  "cat")))))
               :cxn-set lex
               :attributes (:string "cat" :meaning cat))

  (def-fcg-cxn dog-cxn
               ((?dog-word
                 (args (?x))
                 (sem-cat (sem-class physical-entity))
                 (syn-cat (lex-class noun)))
                <-
                (?dog-word
                 (HASH meaning ((dog ?x)))                     
                 --
                 (HASH form ((string ?dog-word  "dog")))))
               :cxn-set lex
               :attributes (:string "dog" :meaning dog))
  
  ;;Grammatical Constructions
  ;; NP -> ART NOUN
  (def-fcg-cxn noun-phrase-cxn
               ((?noun-phrase
                 (args (?x))
                 (sem-cat (sem-class referring-expression))
                 (syn-cat (lex-class noun-phrase))
                 (subunits (?article ?noun))
                 (boundaries ((leftmost-unit ?article)
                              (rightmost-unit ?noun))))
                <-
                (?article
                 (args (?x))
                 (sem-cat (sem-class referent))
                 --
                 (syn-cat (lex-class article)))
                (?noun
                 (args (?x))
                 (sem-cat (sem-class physical-entity))                   
                 --
                 (syn-cat (lex-class noun)))
                (?noun-phrase
                 --
                 (HASH form ((meets ?article ?noun)))))
               :cxn-set phrasal)
  
  ;; VP -> V
  (def-fcg-cxn verb-phrase-cxn
               ((?verb-phrase
                 (args ?args)
                 (sem-cat (sem-class relational-expression))
                 (syn-cat (lex-class verb-phrase)
                          (type ?type))
                 (subunits (?verb))
                 (boundaries ((leftmost-unit ?verb)
                             (rightmost-unit ?verb))))
                <-
                (?verb
                 (args ?args)
                 (sem-cat (sem-class relation))
                 --
                 (syn-cat (lex-class verb)
                          (type ?type))))
               :cxn-set phrasal)
  
  ;; Transitive-clause -> NP VP NP
  (def-fcg-cxn transitive-clause-cxn
               ((?transitive-clause
                 (args (?x ?y))
                 (sem-cat (sem-class predicating-expression))
                 (syn-cat (lex-class transitive-clause))
                 (subunits (?subject-noun-phrase ?verb-phrase ?object-noun-phrase)))
                <-
                (?subject-noun-phrase
                 (args (?x))
                 (sem-cat (sem-class referring-expression))
                 --
                 (syn-cat (lex-class noun-phrase))
                 (boundaries ((rightmost-unit ?rightmost-subject-unit))))
                (?verb-phrase
                 (args (?ev))
                 (sem-cat (sem-class relational-expression))
                 --
                 (syn-cat (lex-class verb-phrase)
                          (type transitive))
                 (boundaries ((leftmost-unit ?leftmost-verb-unit)
                              (rightmost-unit ?rightmost-verb-unit))))
                (?object-noun-phrase
                 (args (?y))
                 (sem-cat (sem-class referring-expression))
                 --
                 (syn-cat (lex-class noun-phrase))
                 (boundaries ((leftmost-unit ?leftmost-object-unit))))
                (?transitive-clause
                 (HASH meaning ((:arg0 ?ev ?x)
                                (:arg1 ?ev ?y)))
                 --
                 (HASH form ((meets ?rightmost-subject-unit ?leftmost-verb-unit)
                             (meets ?rightmost-verb-unit ?leftmost-object-unit)))))
               :cxn-set transitive)

  (def-fcg-cxn intransitive-clause-cxn
               ((?intransitive-clause
                 (args (?x ?y))
                 (sem-cat (sem-class predicating-expression))
                 (syn-cat (lex-class intransitive-clause))
                 (subunits (?subject-noun-phrase ?verb-phrase)))
                <-
                (?subject-noun-phrase
                 (args (?x))
                 (sem-cat (sem-class referring-expression))
                 --
                 (syn-cat (lex-class noun-phrase))
                 (boundaries ((rightmost-unit ?rightmost-subject-unit))))
                (?verb-phrase
                 (args (?ev))
                 (sem-cat (sem-class relational-expression))
                 --
                 (syn-cat (lex-class verb-phrase)
                          (type intransitive))
                 (boundaries ((leftmost-unit ?leftmost-verb-unit))))
                (?intransitive-clause
                 (HASH meaning ((:arg0 ?ev ?x)))
                 --
                 (HASH form ((meets ?rightmost-subject-unit ?leftmost-verb-unit)))))
               :cxn-set intransitive))

(pprint (configuration *fcg-constructions*))


;; Search algorithm: depth-first:
(set-configuration *fcg-constructions* :search-algorithm :depth-first)
(comprehend-and-formulate "the cat eats the mouse")
(pprint (configuration *fcg-constructions*))

;; Search algorithm: breadth-first:
(set-configuration *fcg-constructions* :search-algorithm :breadth-first)
(comprehend-and-formulate "the cat eats the mouse")


;; Search algorithm: random:
(set-configuration *fcg-constructions* :search-algorithm :random)
(comprehend-and-formulate "the cat eats the mouse")

;; Search algorithm: best-first:
(progn
  (set-configuration *fcg-constructions* :search-algorithm :best-first)
  (set-configuration *fcg-constructions* :heuristics '(:nr-of-applied-cxns :nr-of-units-matched))
  (set-configuration *fcg-constructions* :heuristic-value-mode :sum-heuristics-and-parent))

(comprehend-and-formulate "the cat eats the mouse")


;;cxn sets and hashing
(progn
  (set-configuration *fcg-constructions* :search-algorithm :best-first)
  (set-configuration *fcg-constructions* :cxn-supplier-mode :cxn-sets-hashed)
  (set-configuration *fcg-constructions* :heuristics '(:nr-of-applied-cxns :cxn-sets)))

(comprehend "the cat eats the mouse")


