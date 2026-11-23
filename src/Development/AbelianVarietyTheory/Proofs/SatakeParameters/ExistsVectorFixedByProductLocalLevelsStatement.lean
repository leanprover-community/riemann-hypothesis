module

public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsVectorFixedByProductLocalLevels
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RestrictsSelf

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

theorem _root_.GlobalTheory.T.exists_vector_fixed_by_product_localLevels : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U → ∀ (w₀ : HeightOneSpectrum (𝓞 E)) (K : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a)), (∀ w, K w ≤ locU a w) → (∀ w u, ¬ Apart w u → K w = K u) → (∀ w, IsCompact (K w : Set (UA E a))) → (∀ᶠ w in Filter.cofinite, ∀ x ∈ K w, cLoc w x ∈ GlobalTheory.LFun.KGL w (n := a)) → (∀ w, IsOpen ((K w).subgroupOf (locU a w) : Set (locU a w))) → (∀ w, Apart w w₀ → ∃ φ ∈ U, φ ≠ 0 ∧ ∀ x ∈ K w, RU E a x φ = φ) → ∃ φ ∈ U, φ ≠ 0 ∧ ∀ w, Apart w w₀ → ∀ x ∈ K w, RU E a x φ = φ := by
  first | (exact @GlobalTheory.Cong.FixProd.fix_prod) | (exact GlobalTheory.Cong.FixProd.fix_prod) | (intros; apply GlobalTheory.Cong.FixProd.fix_prod  <;> assumption)
