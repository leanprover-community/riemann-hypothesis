module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameEquivApply
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTwistOfTwistingCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeightEmbeddingHarmonicPolynomialsLattices
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MtRead



theorem _root_.GlobalTheory.T.exists_weightEmbedding_harmonicPolynomials_lattices : ∀ (D : D7) (S T : HSp D) (B : GlobalTheory.ExportSeries.Base S T), B.Good → ∀ (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi S n), IdFrame hF P → ∀ (hn : S.rank = n) (K₀ : Type) [Field K₀] (R : Type) [CommRing R] [IsDomain R] (e : FractionRing R →+* ℂ) (f : K₀ →+* FractionRing R) (s : ↥D.LL0 →+* K₀), (∀ x, e (f (s x)) = embLL0 D x) → IsCoefRing (embLL0 D) (labLL0 D) (e.comp (algebraMap R (FractionRing R))).range → ∀ (W₀ : Type) [AddCommGroup W₀] [Module K₀ W₀] (ρ₀ : Representation K₀ (ReciprocityTheory.Aut.GQ D.host.E n) W₀) (lam : D.what₂.Tau → DomWeight n), (∀ τ a, (lam τ).w (Fin.cast hn a) = (B.w.lam τ).w a) → ∀ T₀ : W₀ ≃ₗ[K₀] VV K₀ lam, (∀ (γ : ReciprocityTheory.Aut.GQ D.host.E n) (γ₀ : GL (Fin n) D.host.E), (((γ : GAf D.host.E n) : GL (Fin n) (ReciprocityTheory.Aut.AL D.host.E)) : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)) = (γ₀ : Matrix (Fin n) (Fin n) D.host.E).map Algebra.TensorProduct.includeLeftRingHom → ∀ x, T₀ (ρ₀ γ x) = rhoVr (fun τ => s.comp (labLL0 D τ)) lam γ₀ (T₀ x)) → ∀ (W : Type) [AddCommGroup W] [Module (FractionRing R) W] (ρ : Representation (FractionRing R) (ReciprocityTheory.Aut.GQ D.host.E n) W), (∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (b₀ : Module.Basis ι K₀ W₀) (b₁ : Module.Basis ι (FractionRing R) W), ∀ γ : ReciprocityTheory.Aut.GQ D.host.E n, LinearMap.toMatrix b₁ b₁ (ρ γ) = (LinearMap.toMatrix b₀ b₀ (ρ₀ γ)).map f) → ∃ ω : W →ₛₗ[e] PolF D T.rank S.rank, WtMap B (frameEquiv P) R e ρ ω := by
  first | exact @GlobalTheory.MtRead.WtEmb.exists_wtMap | exact GlobalTheory.MtRead.WtEmb.exists_wtMap | (intros; apply GlobalTheory.MtRead.WtEmb.exists_wtMap <;> assumption)
