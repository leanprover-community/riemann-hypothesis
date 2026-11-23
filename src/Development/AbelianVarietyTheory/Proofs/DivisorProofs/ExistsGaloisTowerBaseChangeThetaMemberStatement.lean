module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisTowerBaseChangeThetaMember
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.exists_galoisTower_baseChange_thetaMember : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), GlobalTheory.GSep.IsAct X₁ act → ∀ (𝔗 : GlobalTheory.GSep.Tower X₁ act) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ → ∃ eps : X₁.S.Gam → ℕ, ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam) (T : X → C → V), 𝔪.Terms x₀ lab T → ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (io : V →+* V'), IsCN V' → Function.Injective io → io.Finite → ∃ 𝔪₂ : ∀ ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V', 𝔗.Ext ev io ev₂ → GlobalTheory.GSep.GMem 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X (fun k => io (t k)) δ, (∀ ev₂ h (zt : 𝔗.X₂.M.Z.presheaf.stalk z₂), 𝔗.X₂.M.stalkHom z₂ zt = algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ → (𝔪₂ ev₂ h).Terms (𝔗.lam x₀) (fun c => 𝔗.lam (lab c)) (fun mu c => ev₂ zt ^ eps (lab c) * io (T mu c))) ∧ ∀ ev₂ h ev₂' h' (σ : 𝔗.X₂.Ω₁ ≃ₐ[X₁.Ω₁] 𝔗.X₂.Ω₁), (∀ x x', 𝔗.X₂.M.stalkHom z₂ x' = σ (𝔗.X₂.M.stalkHom z₂ x) → ev₂' x = ev₂ x') → (∀ x, ∃ x', 𝔗.X₂.M.stalkHom z₂ x' = σ (𝔗.X₂.M.stalkHom z₂ x)) → ∀ a mu, (𝔪₂ ev₂' h').YY a mu ↔ (𝔪₂ ev₂ h).YY (𝔗.gl σ a) mu := by
  first | exact @GlobalTheory.GSep.exists_baseChange_gMem_of_tower | exact GlobalTheory.GSep.exists_baseChange_gMem_of_tower | (intros; apply GlobalTheory.GSep.exists_baseChange_gMem_of_tower <;> assumption)
