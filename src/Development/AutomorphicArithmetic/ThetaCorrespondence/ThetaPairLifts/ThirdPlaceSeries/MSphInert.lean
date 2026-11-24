module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtRows
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverRowsAndMono
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormalIntegrality
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalInertiaOfIsotypic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StandardFrameNonsplitMaxCompactInLevelStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyIrreducible
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MGoodRef
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open GlobalTheory.SphInertRef
noncomputable section
theorem UpperTheory.One.M.sphInert_of_isoTyp_comap_ne_bot : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.LiftRef.ForallRowSideParameters hL fun D _ _ _ a M => ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (S : Submodule ℂ (Formalism.AUTREP.GAf D.host.E D.R.nV → (M D.what₂.mu0 j h1 h2).wt.W)) (hS : NG.IsIrrRep (M D.what₂.mu0 j h1 h2).wt.ρ S), (NG.isoTyp (M D.what₂.mu0 j h1 h2).wt.ρ S).comap (M D.what₂.mu0 j h1 h2).real ≠ ⊥ → SphericalInertData.SphInert D.nd D.naut D.nbc j (a.A.cls j h1 h2 (GlobalTheory.LiftRef.autOf (M D.what₂.mu0 j h1 h2) S hS)) := by
  have hLvl := GlobalTheory.T.standardFrame_nonsplit_maxCompact_in_level
  intro hP hL
  have hG := _root_.UpperTheory.One.M.goodRef_alt hP hL
  unfold _root_.GlobalTheory.LiftRef.ForallRowSideParameters at hG ⊢
  refine GlobalTheory.LiftRef.overRows_and_mono hLvl hG (fun K B f T w Z Wt hX z p0 Y h hg => ?_)
  intro Rw a M tup Q hMA hx j h1 h2 S hS hne w' hw'
  have hgood := hg Rw a M tup Q hMA hx j h1 h2 S hS hne
  obtain ⟨i, rfl⟩ : ∃ i : Fin (w.st Z).toD7.R.m, i.1 + 1 = j := ⟨⟨j - 1, by omega⟩, by simp only; omega⟩
  rw [a.A.sph (i.1 + 1) h1 h2 _ w' (HeightOneSpectrum.under (𝓞 (maximalRealSubfield (w.st Z).toD7.host.E)) w') hw' rfl]
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 hne
  have hry : (M _ _ h1 h2).real y ≠ 0 := fun e =>
    hy0 ((M _ _ h1 h2).real_inj (e.trans (map_zero _).symm))
  obtain ⟨f, hf, hf0, hff⟩ := GlobalTheory.AutUnr.exists_fixed_of_isoTyp _ hS.1.stable
    {κ | κ ∈ Umax (w.st Z).toD7.host.E (w.st Z).toD7.R.nV ∧
      TrivOutside {HeightOneSpectrum.under (𝓞 (maximalRealSubfield (w.st Z).toD7.host.E)) w'} κ} hy hry
    (fun κ hκ => rt_real_eq_of_lev hMA i y κ (h i (hMA.PV i) (hMA.std i) w' hw' κ hκ.1 hκ.2).1
      (h i (hMA.PV i) (hMA.std i) w' hw' κ hκ.1 hκ.2).2)
  exact _root_.UpperTheory.One.M.New.sphMk ⟨f, hf, hf0, fun κ hU htr => hff κ ⟨hU, htr⟩⟩ fun _ => hgood
end
end
