module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleAdmissibleDecomposableCompEquiv
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIrreducibleSmallRepUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArchimedeanUnitaryPointsEquivUnitaryGroup
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryArchimedean
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrreducibleRepIsotypicOfCentraliserFactor
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.DefU

theorem iSup_range_weight_eq_top : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AutSub E n) (τ : E →+* ℂ) (lam : DomWeight n), HasWeightAt π.V τ lam → (⨆ f : Representation.IntertwiningMap ((GlobalTheory.Branching.sqRep ℂ n lam).comp ((cEmb τ).comp (embU n τ).subtype)) (π.rep.comp (embU n τ).subtype), LinearMap.range f.toLinearMap) = ⊤ := by
  intro E _ _ _ n π τ lam h
  obtain ⟨-, f, hf0, hfm, hf⟩ := h
  obtain ⟨e, he⟩ := GlobalTheory.EmbUnitary.exists_equiv_unitaryGroup E n τ
  obtain ⟨r, -, -, hr⟩ := GlobalTheory.DefU.exists_embRet E n τ
  have heq : (GlobalTheory.Branching.sqRep ℂ n lam).comp ((cEmb τ).comp (embU n τ).subtype) =
      (GlobalTheory.Branching.smallRep (GlobalTheory.Branching.unitaryIncl n) lam).comp e.toMulEquiv.toMonoidHom := by
    ext x : 1
    change GlobalTheory.Branching.sqRep ℂ n lam (cEmb τ (x : UA E n)) =
      GlobalTheory.Branching.sqRep ℂ n lam (GlobalTheory.Branching.unitaryIncl n (e x))
    rw [he]
  have hσ : Representation.IsIrreducible ((GlobalTheory.Branching.sqRep ℂ n lam).comp ((cEmb τ).comp (embU n τ).subtype)) := by
    rw [heq]
    exact GlobalTheory.CuspMult.isIrreducible_comp_mulEquiv _ e.toMulEquiv
      (GlobalTheory.Branching.isIrreducible_smallRep_unitary n lam)
  let F : Representation.IntertwiningMap ((GlobalTheory.Branching.sqRep ℂ n lam).comp ((cEmb τ).comp (embU n τ).subtype))
      (π.rep.comp (embU n τ).subtype) :=
    ⟨f.codRestrict π.V hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf x v)⟩
  have hF0 : F ≠ 0 := fun h0 =>
    hf0 (LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun h0 v))
  exact (GlobalTheory.CuspRep.CompUniq.isotypic (UA E n) (embU n τ) π.V _ _ π.rep (embU n τ).subtype _ _
    π.isIrreducible_rep hσ hσ (fun g => ⟨r g, fun y => hr g y⟩) F hF0).1

end GlobalTheory.DefU
