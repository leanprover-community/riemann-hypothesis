module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaFamMono
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.EigV
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalQuot
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PrimCase
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

theorem UpperTheory.V.ML.psiOf :
    Rec → PsiBound := by
  intro hR E Ω _ _ _ _ _ _ _ _ _ _ N _ ρ hρ l _ hl2 hlE O _ _ e he ψ hodd a ha
  haveI : IsGalois ℚ E := inferInstance
  let c : HV.Coef l := ⟨O, inferInstance, inferInstance⟩
  let ψ' : DirichletCharacter (↥c.O) N := MulChar.ofUnitHom (ψ.comp ρ)
  have hcomp : MulChar.ringHomComp ψ' c.O.val.toRingHom = chiOf ρ ψ := by
    ext b
    simp [ψ', chiOf, MulChar.ringHomComp_apply]
  have hord : ¬ l ∣ orderOf ψ' := by
    intro hdiv
    apply hlE
    refine hdiv.trans ?_
    rw [← IsGalois.card_aut_eq_finrank]
    apply orderOf_dvd_of_pow_eq_one
    ext b
    simp only [ψ', MulChar.pow_apply_coe, MulChar.ofUnitHom_coe, MulChar.one_apply_coe]
    have h2 : ψ (ρ b) ^ Fintype.card Gal(E/ℚ) = 1 := by
      rw [← map_pow, pow_card_eq_one, map_one]
    have h3 := congrArg (fun u : (↥O)ˣ => ((u : ↥O) : PadicAlgCl l)) h2
    simpa using h3
  have hodd' : ψ' (-1) = (-1) ^ (e + 1) := by
    have h1 := congrArg (fun χ => χ (-1)) hcomp
    simp only [MulChar.ringHomComp_apply] at h1
    apply Subtype.val_injective
    rw [hodd] at h1
    simpa using h1
  have key := vChar hR Ω l c hl2 N ψ' e he hord hodd' a (by rw [hcomp]; exact ha)
  obtain ⟨_, hker, hlift⟩ := galQuot ℚ E Ω
  have hρσ : ∀ σ : G ℚ Ω, ρ (Chr.cls ℚ Ω N σ) = AlgEquiv.restrictNormalHom E σ := by
    intro σ
    have h1 := hρ (Chr.cls ℚ Ω N σ) σ.toRingEquiv (fun x hx => Chr.cls_spec N σ x hx)
    have h2 := hlift σ
    ext x
    apply (algebraMap E Ω).injective
    exact (h1 x).symm.trans (h2 x)
  have hdir : Chr.dirG ℚ Ω ψ' = ψ.comp (AlgEquiv.restrictNormalHom E) := by
    ext σ
    simp [Chr.dirG, ψ', hρσ]
  obtain ⟨_, hopen, hidx⟩ := galEmbTop ℚ E Ω
  haveI : (galOf ℚ E Ω).Normal := by
    rw [← hker]
    infer_instance
  have hle : galOf ℚ E Ω ≤ (ψ.comp (AlgEquiv.restrictNormalHom E)).ker := by
    rw [← hker]
    intro g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    simp [hg]
  have heig := Chr.eigV ℚ Ω l O e (ψ.comp (AlgEquiv.restrictNormalHom E)) (galOf ℚ E Ω) hopen hle
    (by rw [hidx]; exact hlE)
  have hpsi : psiLen Ω e ψ = Chr.eigL l e (galOf ℚ E Ω) (ψ.comp (AlgEquiv.restrictNormalHom E)) := rfl
  rw [hpsi, heig, ← hdir]
  exact key
