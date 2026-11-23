module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per



private theorem linearIndependent_smul_basis_pairs {Z Q O L V κ σ : Type*} [CommRing Z] [Field Q] [Algebra Z Q] [IsFractionRing Z Q]
    [CommRing O] [Field L] [Algebra O L] [Algebra Z O] [Algebra Q L] [Algebra Z L]
    [IsScalarTower Z O L] [IsScalarTower Z Q L] [AddCommGroup V] [Module L V] [Module O V] [Module Q V]
    [IsScalarTower O L V] [IsScalarTower Q L V] (M : Submodule O V) (b : Module.Basis κ O M)
    (ω : Module.Basis σ Z O) :
    LinearIndependent Q (fun p : σ × κ => (algebraMap O L (ω p.1)) • ((b p.2 : M) : V)) := by
  letI : Module Z V := Module.compHom V (algebraMap Z L)
  haveI : IsScalarTower Z Q V := ⟨fun z q v => by
    show (z • q) • v = algebraMap Z L z • (q • v)
    rw [← algebraMap_smul L (z • q) v, ← algebraMap_smul L q v, smul_smul, Algebra.smul_def z q,
      map_mul, ← IsScalarTower.algebraMap_apply Z Q L]⟩
  haveI : IsScalarTower Z O V := ⟨fun z o v => by
    show (z • o) • v = algebraMap Z L z • (o • v)
    rw [Algebra.smul_def z o, mul_smul, ← algebraMap_smul L (algebraMap Z O z) (o • v),
      ← IsScalarTower.algebraMap_apply Z O L]⟩
  have hc : LinearIndependent O (fun k => ((b k : M) : V)) :=
    b.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have hZ : LinearIndependent Z (fun p : σ × κ => ω p.1 • ((b p.2 : M) : V)) :=
    linearIndependent_smul ω.linearIndependent hc
  have hQ := (LinearIndependent.iff_fractionRing Z Q).mp hZ
  have hf : (fun p : σ × κ => (algebraMap O L (ω p.1)) • ((b p.2 : M) : V)) =
      fun p => ω p.1 • ((b p.2 : M) : V) := funext fun p => algebraMap_smul L (ω p.1) _
  rw [hf]
  exact hQ

private theorem aux {Z Q O L V κ σ : Type*} [CommRing Z] [IsDomain Z] [Field Q] [Algebra Z Q] [IsFractionRing Z Q]
    [CommRing O] [IsDomain O] [Field L] [Algebra O L] [IsFractionRing O L] [Algebra Z O] [Algebra Q L] [Algebra Z L]
    [IsScalarTower Z O L] [IsScalarTower Z Q L] [AddCommGroup V] [Module L V] [Module O V] [Module Q V]
    [IsScalarTower O L V] [IsScalarTower Q L V] (M : Submodule O V) (b : Module.Basis κ O M) (ω : Module.Basis σ Z O) :
    LinearIndependent Q (fun p : σ × κ => (algebraMap O L (ω p.1)) • ((b p.2 : M) : V)) := by
  exact linearIndependent_smul_basis_pairs M b ω

theorem _root_.UpperTheory.KN.linearIndependent_Ql_integerBasis_smul_latticeBasis :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (κ σ : Type) [Fintype κ] [Fintype σ] (b : Module.Basis κ ↥(OL LL) ↥T.L.T) (ω : Module.Basis σ ℤ_[l] ↥(OL LL)), LinearIndependent ℚ_[l] (fun p : σ × κ => ((ω p.1 : ↥(OL LL)) : ↥LL.1) • ((b p.2 : ↥T.L.T) : T.V)) := by
  intro l _ LL T κ σ _ _ b ω
  exact linearIndependent_smul_basis_pairs (Z := ℤ_[l]) (Q := ℚ_[l]) (L := ↥LL.1) T.L.T b ω
