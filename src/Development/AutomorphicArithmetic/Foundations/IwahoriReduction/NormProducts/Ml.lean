module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsZetaSystemFixedExponent
public import Development.AbelianVarietyTheory.Definitions.Foundations.AdmissibleNewformZetaData
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerUnitClassModPrimePowProperties
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CoeffSlD
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CohApi
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.DiamEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.InvApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KmapComp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.OneLeLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SCycZ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.STop0
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.ZetaClassCohomologyCompat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymEx
public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.IsCompactIntegralCoefficients
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA
open scoped Matrix MatrixGroups

theorem UpperTheory.Kd.K4.ml :
    ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ)
      (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l) (ε : Ω →+* ℂ) (X : Tower Ω ε)
      (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ))
      (ψ : ZMod l → Qbar l) (cf : Coef l),
      (∀ r₀, gm r₀ ∈ CongruenceSubgroup.Gamma1 N) → Nat.Coprime l N → l ≠ 2 → 1 ≤ e → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → AdmissibleNewformZetaData ι e gN A W X pr N x c d gm ψ cf →
      ∃ c₁ : ℕ, ∀ c₀ : ℕ, c₁ ≤ c₀ →
      ∃ Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l,
        IsZetaSystemFixedExponent X l pr W e ψ N x c d (2 * e + 1) gm cf c₀ Y ∧
        (∀ r, ShCoc (rhoK W e ψ) (cycMod (F := ℚ) (Ω := Ω) l r)⁻¹ (Y r)) ∧
        (∀ r, Y r = push (redL l r) (Y (r + 1))) ∧ (∀ r y i, Continuous fun s => Y r s y i) ∧ (∀ r s u i, Y r s u i ∈ cf.O) := by
  intro l _ Ω _ _ _ ι e gN A W ε X pr N _ x c d gm ψ cf _ hc hl he _ hA
  obtain ⟨c₁, h⟩ := UpperTheory.Kd.K4.mlOf2 UpperTheory.V.Z.Kato.Sym.symEx UpperTheory.V.Z.Kato.Nb.sApi UpperTheory.V.Z.Kato.Nb.sInvApi UpperTheory.V.Z.Kato.Nb.sBStab
    UpperTheory.V.Z.Kato.Nb.sSlD UpperTheory.V.Z.Kato.Nb.sCohApi UpperTheory.V.Z.Kato.Nb.sCycZ UpperTheory.V.Z.Kato.Nb.sTop0 UpperTheory.V.Z.Kato.Nb.kato_norm_compatible_cyclotomic_tower
    UpperTheory.V.Z.Kato.Nb.katoZetaElement_normCompatible_in_lTower l Ω ε X N e hc hl he
  exact ⟨c₁, fun c₀ h₀ => h c₀ h₀ ι gN A W pr x c d gm ψ cf hA⟩
