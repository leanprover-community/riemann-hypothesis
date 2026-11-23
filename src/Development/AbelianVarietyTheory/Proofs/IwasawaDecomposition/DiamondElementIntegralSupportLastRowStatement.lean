module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiamondElementIntegralSupportLastRow
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix

theorem _root_.GlobalTheory.T.diamondElement_integral_support_lastRow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : Formalism.BasicNotions.CMData F E) (n T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (J : Matrix (Fin n) (Fin n) E) (S : Formalism.L2.Forms.StepLevel F E hc.sig J T f bad) (π : 𝓞 E) (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) (a : ℤ) (δ : UPts hc.sig J (FiniteAdeleRing (𝓞 F) F)), J = 1 → P.under (𝓞 F) = v → (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → w = P ∨ w = conjPrime₂ P) → π ∈ P.asIdeal → π ∉ P.asIdeal ^ 2 → π ∉ (conjPrime₂ P).asIdeal → (∀ x, x ∈ S.Lb ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → π ∣ r)) → (∀ t t' : latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) J S.Lb)), t'.1 = inclE (F := F) (v.adicCompletion F) (π : E) • t.1 → S.fT v hv t' = 0) → IsDia S v hv a δ → (∀ i j, δ.1.1 i j ∈ RInt F E) ∧ (∀ i j, (δ.1⁻¹).1 i j ∈ RInt F E) ∧ (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ≠ v → ∀ i j, adAt F w ((δ.1⁻¹).1 i j) = if i = j then 1 else 0) ∧ ∀ r j : Fin n, r.1 + 1 = n → HasRes P (adAt F P ((δ.1⁻¹).1 r j)) (if j = r then (a : 𝓞 E ⧸ P.asIdeal) else 0) := by
  first | exact @GlobalTheory.Mem.Dil.dia_data | exact GlobalTheory.Mem.Dil.dia_data | (intros; apply GlobalTheory.Mem.Dil.dia_data <;> assumption)
