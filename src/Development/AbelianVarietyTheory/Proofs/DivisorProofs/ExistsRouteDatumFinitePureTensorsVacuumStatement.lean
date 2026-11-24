module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRouteDatumFinitePureTensorsVacuum
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel


theorem _root_.GlobalTheory.T.exists_routeDatum_finite_pureTensors_vacuum : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j))
    (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j)))
    (e : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Num G i j) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsTripleOf W M t i j e Bs Γ X) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om')
    (hv : ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ Bs.v₁),
    ∃ ΦB, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsDatumB W e Γ Θ' ΦB ∧
      ∃ (m : ℕ) (f : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin (G.V (.grid i j)).rank × Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank)))
        (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin (G.V (.grid i j)).rank × Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank) → Fv D.host.F v) → ℂ)
        (φ₀ : (Fin (G.V (.grid i j)).rank × Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank) → Fv D.host.F Bs.v₁) → ℂ),
        ΦB = ∑ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f k) (φ k) ∧ (∀ k v, φ k v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ k, ∀ᶠ v in Filter.cofinite, φ k v = Γ.M'.vac v) ∧
        (∀ k, φ k Bs.v₁ = φ₀) ∧
        ∃ (ι : ((Fin (G.V (.grid i j)).rank × Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank) → Fv D.host.F Bs.v₁) → ℂ) →ₗ[ℂ]
              (Matrix (Fin (G.V (.grid i j)).rank) (Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank)) (Fv D.host.F Bs.v₁) → ℂ))
          (P : GL (Fin (G.V (.grid i j)).rank) (Fv D.host.F Bs.v₁))
          (Λ : Submodule 𝒪[Fv D.host.F Bs.v₁] (Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank) → Fv D.host.F Bs.v₁)) (c : ℂ),
          Γ.M'.IsLinBar Bs.ψ Bs.τ₁ 1 1 ι ∧
          ∀ Y, ι φ₀ Y = c * (matLat (Fin (G.V (.grid i j)).rank) Λ : Set _).indicator 1 (P.val * Y) := by
  first | exact @GlobalTheory.SmallDatum.exists_datum_pure_linBar | exact GlobalTheory.SmallDatum.exists_datum_pure_linBar | (intros; apply GlobalTheory.SmallDatum.exists_datum_pure_linBar <;> assumption)
