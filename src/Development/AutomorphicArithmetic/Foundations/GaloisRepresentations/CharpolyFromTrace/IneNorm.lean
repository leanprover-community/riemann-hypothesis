module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.UnlinkedOfType
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalArtinCompNormCompat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.LimitEig
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.HasTypeVecIff

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open scoped Pointwise
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel UpperTheory.Gal.TypesAndIwahori GlobalTheory.Cong UpperTheory.Gal.NearKilling

section
variable {E M Ω : Type} [Field E] [NumberField E] [Field M] [NumberField M] [Field Ω] [Algebra E M] [Algebra E Ω] [Algebra M Ω] [IsScalarTower E M Ω]

private theorem res_mem_Ine_iff (A : ValuationSubring Ω) (σ : G M Ω) :
    (AlgEquiv.restrictScalarsHom E σ : G E Ω) ∈ Ine (F := E) A ↔ σ ∈ Ine (F := M) A := (Iff.rfl)

end

theorem UpperTheory.Gal.NearKilling.ineNorm :
    IneNorm := by
  intro E M Ω _ _ _ _ _ _ _ _ _ _ _ A v w _ h h' hfix art art' ha ha'
  have hl : ∀ s : Ine (F := E) A, ∃ t : G M Ω, AlgEquiv.restrictScalarsHom E t = (s : G E Ω) := by
    intro s
    exact ⟨{ (s : G E Ω) with commutes' := fun x => hfix s s.2 x }, by ext x; rfl⟩
  have hr : ∀ t : Ine (F := M) A, (AlgEquiv.restrictScalarsHom E (t : G M Ω) : G E Ω) ∈ Ine (F := E) A :=
    fun t => (res_mem_Ine_iff (E := E) (M := M) A (t : G M Ω)).2 t.2
  obtain ⟨r, hrv⟩ : ∃ r : Ine (F := M) A →* Ine (F := E) A,
      ∀ t, (r t : G E Ω) = AlgEquiv.restrictScalarsHom E (t : G M Ω) :=
    ⟨MonoidHom.codRestrict ((AlgEquiv.restrictScalarsHom E).comp (Ine (F := M) A).subtype)
      (Ine (F := E) A) hr, fun t => rfl⟩
  have hbij : Function.Bijective r := by
    constructor
    · intro a b hab
      apply Subtype.ext
      ext x
      have hab' := congrArg Subtype.val hab
      rw [hrv, hrv] at hab'
      exact DFunLike.congr_fun hab' x
    · intro s
      obtain ⟨t, ht⟩ := hl s
      have htm : t ∈ Ine (F := M) A := (res_mem_Ine_iff (E := E) (M := M) A t).1 (ht ▸ s.2)
      exact ⟨⟨t, htm⟩, Subtype.ext ((hrv _).trans ht)⟩
  obtain ⟨e, he⟩ : ∃ e : Ine (F := E) A ≃* Ine (F := M) A, ∀ s, r (e s) = s :=
    ⟨(MulEquiv.ofBijective r hbij).symm, fun s => (MulEquiv.ofBijective r hbij).apply_symm_apply s⟩
  have key : ∀ s, (AlgEquiv.restrictScalarsHom E ((e s : Ine (F := M) A) : G M Ω) : G E Ω) = s := by
    intro s
    rw [← hrv, he]
  refine ⟨e, key, fun s => ?_⟩
  exact GlobalTheory.ArtinNormU.localArtin_normU E M Ω A v w h h' art art' ha ha' _ _
    (fun z => (DFunLike.congr_fun (key s) z).symm)
