module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.OhatCompact
public import Mathlib.Algebra.Module.Lattice.Full
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeStabilizerConjFiniteAdeleGLIntegral
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL


theorem _root_.GlobalTheory.T.exists_lattice_stabilizer_conj_finiteAdeleGL_integral : ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)), ∃ Λ : Submodule (𝓞 F) (Fin n → F), Submodule.IsFullLattice F Λ ∧ ∀ γ : GL (Fin n) F, (∀ y, (γ : Matrix (Fin n) (Fin n) F) *ᵥ y ∈ Λ ↔ y ∈ Λ) → s⁻¹ * PIW.ClassFinD.glIncl F n γ * s ∈ PIW.ClassFinD.KGL F n := by
  intro F _ _ n s
  let Λ := GlobalTheory.StabLat.lat F s
  have hΛ : Submodule.IsFullLattice F Λ :=
    { toIsLattice := Submodule.IsLattice.of_fg F (GlobalTheory.StabLat.lat_fg s)
      span_eq_top := GlobalTheory.StabLat.lat_span s }
  refine ⟨Λ, hΛ, fun γ hγ => ⟨GlobalTheory.StabLat.matInt_conj s γ fun y hy => (hγ y).2 hy, ?_⟩⟩
  have hinv : (s⁻¹ * PIW.ClassFinD.glIncl F n γ * s)⁻¹ =
      s⁻¹ * PIW.ClassFinD.glIncl F n γ⁻¹ * s := by
    rw [map_inv]; group
  rw [hinv]
  refine GlobalTheory.StabLat.matInt_conj s γ⁻¹ fun y hy => ?_
  rw [← hγ, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  exact hy
