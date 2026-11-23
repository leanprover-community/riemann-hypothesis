module

public import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.RatZOfTests
public import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.CoordRat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Module NumberField
open scoped InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Rat

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Cx.CxData

theorem solve_spec {E : Type} [AddCommGroup E] [Module ℂ E] {n : ℕ} (f : (Fin n → ℂ) →ₗ[ℂ] E) (e : E)
    (he : e ∈ LinearMap.range f) : f (solve f e) = e := by
  have hex : ∃ y, f y = e := he
  unfold solve
  rw [dite_eq_left hex]
  exact hex.choose_spec

theorem lin_single {E : Type} [AddCommGroup E] [Module ℂ E] {n : ℕ} (v : Fin n → E) (k : Fin n) :
    lin v (Pi.single k 1) = v k := by
  simp [lin, Fintype.linearCombination_apply_single]

theorem ratMuOfRowTest : RatMuOfRowTest := by
  intro K _ _ _ Bs A X fc cr b hT hH2
  obtain ⟨N, ψ, hψ, hr⟩ := hT
  obtain ⟨hinj0, hall, -⟩ := hH2
  intro t i k
  have hmem : X.iC cr b t (Pi.single k 1) ∈ LinearMap.range (X.iC cr b Bs.μ0) := by
    rw [← (hall t).2]; exact LinearMap.mem_range_self _ _
  have key := coord_rat Bs.v0.embedding ψ hψ (X.iC cr b Bs.μ0) hinj0
    (fun j l => by rw [CxData.iC, lin_single]; exact hr _ _ _)
    (solve (X.iC cr b Bs.μ0) (X.iC cr b t (Pi.single k 1)))
    (fun j => by rw [solve_spec _ _ hmem, CxData.iC, lin_single]; exact hr _ _ _) i
  obtain ⟨a, ha⟩ := key
  exact ⟨a, by simpa [CxData.rowMatC, relMat] using ha⟩

end Formalism.IndefR.Rat
