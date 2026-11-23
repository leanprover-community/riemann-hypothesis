module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.FiniteEtaleSurjectiveOfPullback
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptLatticeBaseChange
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
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GenUIsGenFam

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

theorem _root_.GlobalTheory.T.hodgeCpt_lattice_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (x : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S x) (τ : CMType H) (X' : Scheme.{0}) (G : Type) [Field G] [Algebra Ω G] (ξ' : Spec (CommRingCat.of G) ⟶ X') (pr : X' ⟶ 𝔐.X) (Li' : Type) [AddCommGroup Li'] [Module G Li'] (j : 𝔐.Li →+ Li') (bO : Module.Basis (Fin D.q) Ω (Module.Dual Ω (𝔐.Vgen (.inr τ)))) (v : Fin D.q → 𝔐.Vgen (.inr τ)) (u : Matrix (Fin D.q) (Fin D.q) G), IsExtOver (algebraMap Ω G) j → GlobalTheory.CompanionTheory.Ar.Dominates ξ' 𝔐.ξ pr (algebraMap Ω G) → (∀ a b, bO a (v b) = if a = b then 1 else 0) → (∀ a, u a a = 1) → (∀ a b, a < b → u a b = 0) → ((omBundle 𝔐 τ).pull ξ' pr (TensorProduct.mk Ω G (Module.Dual Ω (𝔐.Vgen (.inr τ))) 1).toAddMonoidHom).IsFlagVBOn Set.univ (fun k => ∑ l, u l k • TensorProduct.mk Ω G (Module.Dual Ω (𝔐.Vgen (.inr τ))) 1 (bO l)) → ((𝔐.V (.inr τ)).pull ξ' pr j).IsFlagVBOn Set.univ (fun k => colFrame (fun a => j (v a)) uᵀ⁻¹ k.rev) := by
  exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl.flags_dual_of_flags_pull
