module

public import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSmulMemSupLattice
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.IndefR.Arith

namespace GlobalTheory

theorem supLattice_localisation_of_unitBall (LL Ks WL G : Type) [Field LL] [NumberField LL] [Field Ks]
    [NumberField Ks] [Algebra Ks LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
    [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL] (W : (LL →+* ℂ) → Type) [∀ σ, NormedAddCommGroup (W σ)]
    [∀ σ, InnerProductSpace ℂ (W σ)] [Group G] (Φ : FormsL LL Ks WL W G)
    (hspan : Submodule.span Ks (Φ.MK : Set WL) = Φ.WK) (la : HeightOneSpectrum (𝓞 Ks)) (f : Φ.WK)
    (hf : ∀ y : Φ.Pt la, Φ.nrm la y f ≤ 1) :
    ∃ s : 𝓞 Ks, s ∉ la.asIdeal ∧ s • (f : WL) ∈ Φ.MK := by
  first
  | exact @_root_.GlobalTheory.DenominatorExistenceTwistedOperators.exists_smul_mem_supLattice
  | exact _root_.GlobalTheory.DenominatorExistenceTwistedOperators.exists_smul_mem_supLattice
  | (apply _root_.GlobalTheory.DenominatorExistenceTwistedOperators.exists_smul_mem_supLattice <;> assumption)
  | (intros; apply _root_.GlobalTheory.DenominatorExistenceTwistedOperators.exists_smul_mem_supLattice <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DenominatorExistenceTwistedOperators.exists_smul_mem_supLattice <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DenominatorExistenceTwistedOperators.exists_smul_mem_supLattice ..)

end GlobalTheory
