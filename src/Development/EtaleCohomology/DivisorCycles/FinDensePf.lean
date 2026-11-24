module

public import Development.EtaleCohomology.DivisorCycles.CycleCount
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div

namespace LateralTheory.DivDb.FinDensePf

theorem cont_ev {Γ K : Type} [TopologicalSpace Γ] [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    (n : ℕ) (x : Γ → Matrix (Fin n) (Fin n) K) (hx : Continuous x) (f : LateralTheory.DivDb.MP K n) :
    Continuous (fun g => LateralTheory.DivDb.ev (x g) f) := by
  have h1 : Continuous (fun g => (fun p : Fin n × Fin n => x g p.1 p.2)) :=
    continuous_pi fun p => hx.matrix_elem p.1 p.2
  exact (MvPolynomial.continuous_eval f).comp h1

end LateralTheory.DivDb.FinDensePf

namespace LateralTheory.DivDb

theorem FinDense_of (hSep : SepPoly) (hOC : OpenCoset) : FinDense := by
  intro Γ K _ _ _ _ _ _ _ _ _ n r hr hU
  obtain ⟨f, hf⟩ := hSep K n
  have hset : {g : Γ | (r g : Mat K n).charpoly.Separable} = {g | ev (r g : Mat K n) f ≠ 0} := by
    ext g; exact hf _
  rw [hset]
  have hc := LateralTheory.DivDb.FinDensePf.cont_ev n (fun g => (r g : Mat K n)) hr f
  refine ⟨isOpen_ne_fun hc continuous_const, ?_⟩
  rw [dense_iff_inter_open]
  intro O hO hne
  by_contra hemp
  have hz : ∀ g ∈ O, ev (r g : Mat K n) f = 0 := by
    intro g hg
    by_contra h
    exact hemp ⟨g, hg, h⟩
  obtain ⟨U, hUn, hUf, g, hg⟩ := hOC Γ K n r f O hO hne hz
  obtain ⟨u, hu, hs⟩ := hU U hUn hUf g
  exact (hf _).1 hs (hg u hu)

end LateralTheory.DivDb
