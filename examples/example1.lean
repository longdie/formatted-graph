import FormattedGraph
import Mathlib.Data.String.Basic

/-!
# Euclid's theorem blueprint

A dependency graph for Mathlib's `Nat.exists_infinite_primes`. The graph
records the construction, the contradiction branch, and the final result.
-/

namespace FormattedGraph.Examples.Example1

structure NodeId where
  value : String
deriving DecidableEq, Repr

inductive EdgeId where
  | inputToCandidate
  | candidateToNontrivial
  | candidateToChoice
  | nontrivialToPrime
  | choiceToPrime
  | choiceToDividesCandidate
  | inputToAssumption
  | choiceToAssumption
  | assumptionToDividesFactorial
  | primeToDividesFactorial
  | dividesCandidateToOne
  | dividesFactorialToOne
  | primeToContradiction
  | dividesOneToContradiction
  | contradictionToBound
  | primeToConclusion
  | boundToConclusion
deriving DecidableEq, Repr

instance : LinearOrder NodeId :=
  LinearOrder.lift' (fun node => node.value) (by
    intro a b h
    cases a
    cases b
    simp_all)

def EdgeId.rank : EdgeId → Nat
  | .inputToCandidate => 0
  | .candidateToNontrivial => 1
  | .candidateToChoice => 2
  | .nontrivialToPrime => 3
  | .choiceToPrime => 4
  | .choiceToDividesCandidate => 5
  | .inputToAssumption => 6
  | .choiceToAssumption => 7
  | .assumptionToDividesFactorial => 8
  | .primeToDividesFactorial => 9
  | .dividesCandidateToOne => 10
  | .dividesFactorialToOne => 11
  | .primeToContradiction => 12
  | .dividesOneToContradiction => 13
  | .contradictionToBound => 14
  | .primeToConclusion => 15
  | .boundToConclusion => 16

instance : LinearOrder EdgeId :=
  LinearOrder.lift' EdgeId.rank (by
    intro a b h
    cases a <;> cases b <;> simp_all [EdgeId.rank])

structure NodeInfo where
  label : String
  category : String
  description : String
deriving Repr

structure EdgeInfo where
  label : String
  description : String
deriving Repr

instance : Data.NodeData NodeId where
  data_type := NodeInfo

instance : Data.EdgeData EdgeId where
  data_type := EdgeInfo

instance : FormattedGraph.NodeRenderer NodeId where
  id node := node.value
  render _ data :=
    pure <| FormattedGraph.NodePresentation.text data.label <|
      some (.text s!"{data.category}: {data.description}")

instance : FormattedGraph.EdgeRenderer EdgeId where
  render _ data :=
    pure <| FormattedGraph.EdgePresentation.text data.label <|
      some (.text data.description)

def arbitraryN : NodeId := ⟨"arbitrary-n"⟩
def candidate : NodeId := ⟨"factorial-plus-one"⟩
def nontrivial : NodeId := ⟨"candidate-not-one"⟩
def choosePrime : NodeId := ⟨"choose-min-factor"⟩
def prime : NodeId := ⟨"factor-is-prime"⟩
def dividesCandidate : NodeId := ⟨"factor-divides-candidate"⟩
def contraryAssumption : NodeId := ⟨"contrary-bound"⟩
def dividesFactorial : NodeId := ⟨"factor-divides-factorial"⟩
def dividesOne : NodeId := ⟨"factor-divides-one"⟩
def contradiction : NodeId := ⟨"contradiction"⟩
def lowerBound : NodeId := ⟨"lower-bound"⟩
def conclusion : NodeId := ⟨"prime-above-n"⟩

def endpoints : EdgeId → NodeId × NodeId
  | .inputToCandidate => (arbitraryN, candidate)
  | .candidateToNontrivial => (candidate, nontrivial)
  | .candidateToChoice => (candidate, choosePrime)
  | .nontrivialToPrime => (nontrivial, prime)
  | .choiceToPrime => (choosePrime, prime)
  | .choiceToDividesCandidate => (choosePrime, dividesCandidate)
  | .inputToAssumption => (arbitraryN, contraryAssumption)
  | .choiceToAssumption => (choosePrime, contraryAssumption)
  | .assumptionToDividesFactorial =>
      (contraryAssumption, dividesFactorial)
  | .primeToDividesFactorial => (prime, dividesFactorial)
  | .dividesCandidateToOne => (dividesCandidate, dividesOne)
  | .dividesFactorialToOne => (dividesFactorial, dividesOne)
  | .primeToContradiction => (prime, contradiction)
  | .dividesOneToContradiction => (dividesOne, contradiction)
  | .contradictionToBound => (contradiction, lowerBound)
  | .primeToConclusion => (prime, conclusion)
  | .boundToConclusion => (lowerBound, conclusion)

def euclidBlueprint : GraphWithData.Result endpoints :=
  GraphWithData.Builder.build do
    GraphWithData.Builder.addNode arbitraryN
      { label := "Arbitrary n"
        category := "Input"
        description := "Fix an arbitrary natural number n." }
    GraphWithData.Builder.addNode candidate
      { label := "N = n! + 1"
        category := "Construction"
        description := "Define the candidate N to be n! + 1." }
    GraphWithData.Builder.addNode nontrivial
      { label := "N != 1"
        category := "Arithmetic fact"
        description := "Factorial positivity implies that N is not 1." }
    GraphWithData.Builder.addNode choosePrime
      { label := "p = minFac N"
        category := "Construction"
        description := "Choose p as the least prime factor of N." }
    GraphWithData.Builder.addNode prime
      { label := "p is prime"
        category := "Prime factor fact"
        description := "Since N != 1, minFac_prime proves that p is prime." }
    GraphWithData.Builder.addNode dividesCandidate
      { label := "p divides N"
        category := "Prime factor fact"
        description := "The theorem minFac_dvd shows that p divides N." }
    GraphWithData.Builder.addNode contraryAssumption
      { label := "Assume p < n"
        category := "Contradiction branch"
        description := "Assume that the chosen prime lies below n." }
    GraphWithData.Builder.addNode dividesFactorial
      { label := "p divides n!"
        category := "Divisibility fact"
        description := "From p < n, dvd_factorial gives p divides n!." }
    GraphWithData.Builder.addNode dividesOne
      { label := "p divides 1"
        category := "Derived contradiction"
        description := "Dividing n! and n! + 1 forces p to divide 1." }
    GraphWithData.Builder.addNode contradiction
      { label := "Contradiction"
        category := "Contradiction"
        description := "A prime number cannot divide 1." }
    GraphWithData.Builder.addNode lowerBound
      { label := "n <= p"
        category := "Bound"
        description := "The contradictory assumption is false, so n <= p." }
    GraphWithData.Builder.addNode conclusion
      { label := "Prime above n"
        category := "Conclusion"
        description := "There exists a prime p satisfying n <= p." }

    GraphWithData.Builder.addEdge .inputToCandidate
      { label := "construct"
        description := "Build a number larger than the factorial." }
    GraphWithData.Builder.addEdge .candidateToNontrivial
      { label := "positive"
        description := "Use factorial positivity." }
    GraphWithData.Builder.addEdge .candidateToChoice
      { label := "minFac"
        description := "Take the least prime factor of the candidate." }
    GraphWithData.Builder.addEdge .nontrivialToPrime
      { label := "premise"
        description := "minFac_prime requires the number to differ from 1." }
    GraphWithData.Builder.addEdge .choiceToPrime
      { label := "minFac_prime"
        description := "The least factor is prime." }
    GraphWithData.Builder.addEdge .choiceToDividesCandidate
      { label := "minFac_dvd"
        description := "The least factor divides its input." }
    GraphWithData.Builder.addEdge .inputToAssumption
      { label := "compare"
        description := "The contradictory bound compares p with n." }
    GraphWithData.Builder.addEdge .choiceToAssumption
      { label := "suppose"
        description := "Start a contradiction argument about p." }
    GraphWithData.Builder.addEdge .assumptionToDividesFactorial
      { label := "dvd_factorial"
        description := "A positive p below n divides n!." }
    GraphWithData.Builder.addEdge .primeToDividesFactorial
      { label := "positive"
        description := "Primality supplies the required positivity of p." }
    GraphWithData.Builder.addEdge .dividesCandidateToOne
      { label := "subtract"
        description := "Use divisibility of n! + 1." }
    GraphWithData.Builder.addEdge .dividesFactorialToOne
      { label := "subtract"
        description := "Use divisibility of n!." }
    GraphWithData.Builder.addEdge .primeToContradiction
      { label := "not_dvd_one"
        description := "Primality rules out divisibility of 1." }
    GraphWithData.Builder.addEdge .dividesOneToContradiction
      { label := "impossible"
        description := "The derived divisibility conflicts with primality." }
    GraphWithData.Builder.addEdge .contradictionToBound
      { label := "discharge"
        description := "Reject p < n and conclude n <= p." }
    GraphWithData.Builder.addEdge .primeToConclusion
      { label := "combine"
        description := "The witness must be prime." }
    GraphWithData.Builder.addEdge .boundToConclusion
      { label := "combine"
        description := "The witness must be at least n." }

#check euclidBlueprint

#show_graph euclidBlueprint

end FormattedGraph.Examples.Example1
