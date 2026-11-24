module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaFamMono
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.ClassFix
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

theorem UpperTheory.V.Chr.levGal :
    ∀ (E : Type) [Field E] [NumberField E] (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ), HasLevel E N H → IsAbelianGalois ℚ E ∧ Module.finrank ℚ E = H.index ∧
          ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra E Ω], galOf ℚ E Ω = levH ℚ Ω H ∧ (levH ℚ Ω H).index = H.index ∧ IsOpen (levH ℚ Ω H : Set (G ℚ Ω)) := by
  intro E _ _ N _ H hlev
  obtain ⟨j, ζ, hζ, hj⟩ := hlev
  haveI : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) :=
    CyclotomicField.isCyclotomicExtension N ℚ
  haveI : IsAbelianGalois ℚ (CyclotomicField N ℚ) :=
    IsCyclotomicExtension.isAbelianGalois {N} ℚ (CyclotomicField N ℚ)
  have hfs : KStar.TotallyRealRoots.fieldSubgroup N (CyclotomicField N ℚ) j.fieldRange = H := by
    ext u
    unfold KStar.TotallyRealRoots.fieldSubgroup
    rw [Subgroup.mem_map_equiv]
    set τ := (IsCyclotomicExtension.Rat.galEquivZMod N (CyclotomicField N ℚ)).symm u with hτdef
    have hu : IsCyclotomicExtension.Rat.galEquivZMod N (CyclotomicField N ℚ) τ = u := by
      rw [hτdef]
      exact MulEquiv.apply_symm_apply _ u
    have hτ : τ ζ = ζ ^ (u : ZMod N).val := by
      rw [IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq N _ τ hζ.pow_eq_one, hu]
    rw [← hj τ u hτ, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h x
      exact h (j x) ⟨x, rfl⟩
    · rintro h _ ⟨x, rfl⟩
      exact h x
  have hfr : Module.finrank ℚ j.fieldRange = Module.finrank ℚ E := by
    rw [(AlgEquiv.ofInjectiveField j).toLinearEquiv.finrank_eq]
    rfl
  have hfin : Module.finrank ℚ E = H.index := by
    rw [← hfr, IntermediateField.finrank_eq_fixingSubgroup_index, ← hfs]
    unfold KStar.TotallyRealRoots.fieldSubgroup
    exact (Subgroup.index_map_of_bijective (MulEquiv.bijective _) _).symm
  refine ⟨IsAbelianGalois.of_algHom j, hfin, ?_⟩
  intro Ω _ _ _ _
  haveI : IsScalarTower ℚ E Ω := inferInstance
  haveI : IsAlgClosure E Ω :=
    ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) E⟩
  have heq : galOf ℚ E Ω = levH ℚ Ω H := by
    ext σ
    rw [mem_galOf]
    unfold levH
    rw [Subgroup.mem_comap, ← hfs]
    exact LDataCardLeFinrank.classFix E Ω N (CyclotomicField N ℚ) j σ.toRingEquiv (cls ℚ Ω N σ)
      (fun z hz => cls_spec N σ z hz)
  obtain ⟨-, hopen, hidx⟩ := galEmbTop ℚ E Ω
  refine ⟨heq, ?_, ?_⟩
  · rw [← heq, hidx, hfin]
  · rw [← heq]
    exact hopen
