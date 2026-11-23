module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MapFinNeg
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeHasRigidificationStatement
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SqTower.StageExists

theorem hasSignature_map_conj {n p q : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.UG.HasSignature M p q) :
    Formalism.UG.HasSignature (M.map (starRingEnd ℂ)) p q := by
  obtain ⟨e, P, hP⟩ := h
  refine ⟨e, Matrix.GeneralLinearGroup.map (starRingEnd ℂ) P, ?_⟩
  have := congrArg (fun A => Matrix.map A (starRingEnd ℂ)) hP
  simp only [Matrix.map_mul] at this
  have hJ : (Formalism.UG.Jpq p q : Matrix _ _ ℂ).map (starRingEnd ℂ) = Formalism.UG.Jpq p q := by
    ext (a | a) (b | b) <;> simp [Formalism.UG.Jpq, Matrix.one_apply, apply_ite]
  rw [hJ] at this
  exact this

def withIdx {D : D7} (V : HSp D) (p : ℕ) : HSp D := { V with sig := fun _ => (V.rank - p, p) }

theorem withIdx_sigOK {D : D7} {V : HSp D} {p : ℕ} (h : NegIdx V p) : (withIdx V p).SigOK := by
  intro σ
  show Formalism.UG.HasSignature (V.gram.map σ) (V.rank - p) p
  obtain ⟨τ, hσ | hσ⟩ := GlobalTheory.DefiniteMult.exists_tauE_or_conj D σ
  · subst hσ
    simpa [gramAt] using h τ
  · subst hσ
    have h1 := hasSignature_map_conj (by simpa [gramAt] using h τ)
    rw [Matrix.map_map] at h1
    exact h1


open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle in
theorem rig_exists {D : D7} {V : HSp D} {p : ℕ} (h : NegIdx V p) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hΛ : IsSelfDualC V Λ) : ∃ r : Rig V, r.Λ = Λ ∧ r.Is := by
  obtain ⟨r, e, hr⟩ := GlobalTheory.T.self_dual_lattice_has_rigidification D (withIdx V p) Λ (withIdx_sigOK h) hΛ
  exact ⟨⟨r.Λ, r.β, r.s, r.B⟩, e, hr⟩


open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle in
theorem vac_exists {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {S WW : HSp D} {p q : ℕ} (hS : NegIdx S p) (hW : NegIdx WW q) {r : Rig S} {rW : Rig WW} (h : r.Is) (h' : rW.Is) :
    (∃ f, IsVacO ψ θ (neg S) WW (fun τ => -r.s τ) rW.s r.Λ rW.Λ f) ∧ ∃ f, IsVacO ψ θ S WW r.s rW.s r.Λ rW.Λ f := by
  have hneg : IsSelfDualC (neg S) r.Λ := by
    refine ⟨h.1.1, fun y => (h.1.2 y).trans (forall₂_congr fun x _ => ⟨fun ⟨c, hc⟩ => ⟨-c, ?_⟩, fun ⟨c, hc⟩ => ⟨-c, ?_⟩⟩)⟩
    · simp [neg_gram, hc]
    · simp [neg_gram] at hc ⊢
      exact neg_eq_iff_eq_neg.2 hc
  constructor
  · obtain ⟨f, h0, h1, ⟨a, b, c, d⟩, h2, h3, h4⟩ := GlobalTheory.VacuumO.vacExists D ψ θ hψ hθ (neg (withIdx S p)) (withIdx WW q) (fun τ => -r.s τ) rW.s
      (sigOK_sgn true (withIdx_sigOK hS)) (withIdx_sigOK hW) (fun τ => isCartanInv_sgn true S τ (h.2.2 τ).1)
      (fun τ => (h'.2.2 τ).1) r.Λ rW.Λ hneg h'.1
    exact ⟨f, h0, h1, ⟨a, b, c, d⟩, h2, h3, h4⟩
  · obtain ⟨f, h0, h1, ⟨a, b, c, d⟩, h2, h3, h4⟩ := GlobalTheory.VacuumO.vacExists D ψ θ hψ hθ (withIdx S p) (withIdx WW q) r.s rW.s
      (withIdx_sigOK hS) (withIdx_sigOK hW) (fun τ => (h.2.2 τ).1) (fun τ => (h'.2.2 τ).1) r.Λ rW.Λ h.1 h'.1
    exact ⟨f, h0, h1, ⟨a, b, c, d⟩, h2, h3, h4⟩


end GlobalTheory.SqTower.StageExists

end
