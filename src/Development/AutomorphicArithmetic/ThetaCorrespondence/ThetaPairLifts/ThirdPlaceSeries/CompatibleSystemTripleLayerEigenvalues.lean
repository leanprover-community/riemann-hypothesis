module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeqRationalDataOfEigen
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtMemImpAltAlt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigOfRatAd
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeAlgebraHasStableSublayer
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalGaloisPsiLevelAtPlace
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ParInBuilt
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
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EigenCompatibleOfBadSet

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.RowTriple.Lay.EigCopy

theorem eigenvalues_at_member_tripleLayer_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ c => ∀ (S : RatDat (w.D Z).ntw) (hL' : ∀ j, ℕ → PlE (w.D Z).host → Module.End (w.D Z).what₂.LL (S.WL j)) (eig : ℕ → (w.D Z).what₂.FT → ℕ → PlE (w.D Z).host → ↥(w.D Z).LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod ((w.D Z).host.g kk)) →* (↥(w.D Z).LL0)ˣ), HEq S (ratL c.a.nt.L c.a.nt.S) → HEq hL' c.a.nt.hL → HEq eig c.a.nt.eig → HEq θ c.a.nt.θ → ∃ Sb : Finset (PlE (w.D Z).host), (∀ i, Sb ⊆ (w.D Z).ntw.S0 i) ∧ ∀ Rw : RowSide (w.D Z), HEq Rw.locR c.a.nt.A.row.locR → GlobalTheory.TwInputs.EigTrue (w.D Z) (TC.cf w.I w.l Z) Rw Sb eig ∧ GlobalTheory.TwInputs.EigOcc (w.D Z) S θ hL' Sb eig := by
  intro hN hS hL
  refine _root_.GlobalTheory.GalLoc.atMem_mono (_root_.GlobalTheory.GalLoc.atMem_and' (_root_.GlobalTheory.T.exists_superset_low_heckeRd_of_subset_S0 hN hS hL) (_root_.GlobalTheory.T.exists_theta_heq_lvlPsi_at_members hN hS hL)) ?_
  intro K B f T w Z Wt p0 t nch n xd c hE H S hL' eig θ hS' hhL heig hθ
  obtain ⟨H2, H3⟩ := H
  obtain ⟨e⟩ := hE
  have e' : _root_.GlobalTheory.HeightCounting.RealExpansionExtraData (D := (w.st Z).toD7) c.row t.r.z.geo xd := e
  obtain ⟨Sb, eg, hSb, heq, hAd⟩ := e'.eig
  obtain ⟨Sb', hsub, hS0, hlow, hrd⟩ := H2 Sb hSb
  obtain ⟨θ0, hθ0, hψ⟩ := H3
  obtain ⟨Rw0, hRw0, ⟨hpar⟩⟩ := _root_.GlobalTheory.RowTriple.Lay.EigCopy.parIn_built_alt c.a.nt _ c.row.rep_eq
  have hT := _root_.GlobalTheory.TwInputs.Eig.eigTrue_of_read hL t.r.Y t.r.z.pins.char.base.lev hpar.T Rw0 hpar.row hAd hsub hlow
  have hO := GlobalTheory.TwInputs.Eig.eigOcc t.r.Y t.r.z.pins.char.base.lev t.r.intersectionNumber_baseChange.prim.unif t.r.z.pins.char.base.models.HW
    t.r.z.good.2 hψ hAd hsub hlow hrd
  rw [t.r.z.lev.C] at hT
  obtain rfl : S = _ := eq_of_heq (hS'.trans c.row.S_eq)
  obtain rfl : hL' = c.row.hecke.hL := eq_of_heq (hhL.trans c.row.hL_eq)
  obtain rfl : eig = eg := eq_of_heq (heig.trans heq)
  obtain rfl : θ = θ0 := eq_of_heq (hθ.trans hθ0.symm)
  refine ⟨Sb', hS0, fun Rw hRw => ⟨eigTrue_congr ?_ hT, hO⟩⟩
  exact eq_of_heq (hRw0.trans hRw.symm)
end GlobalTheory.RowTriple.Lay.EigCopy
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

theorem _root_.GlobalTheory.T.compatibleSystem_tripleLayer_eigenvalues_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ c => ∀ (S : RatDat (w.D Z).ntw) (hL' : ∀ j, ℕ → PlE (w.D Z).host → Module.End (w.D Z).what₂.LL (S.WL j)) (eig : ℕ → (w.D Z).what₂.FT → ℕ → PlE (w.D Z).host → ↥(w.D Z).LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod ((w.D Z).host.g kk)) →* (↥(w.D Z).LL0)ˣ), HEq S (ratL c.a.nt.L c.a.nt.S) → HEq hL' c.a.nt.hL → HEq eig c.a.nt.eig → HEq θ c.a.nt.θ → ∃ Sb : Finset (PlE (w.D Z).host), (∀ i, Sb ⊆ (w.D Z).ntw.S0 i) ∧ ∀ Rw : RowSide (w.D Z), HEq Rw.locR c.a.nt.A.row.locR → GlobalTheory.TwInputs.EigTrue (w.D Z) (TC.cf w.I w.l Z) Rw Sb eig ∧ GlobalTheory.TwInputs.EigOcc (w.D Z) S θ hL' Sb eig := by
  first | exact @_root_.GlobalTheory.RowTriple.Lay.EigCopy.eigenvalues_at_member_tripleLayer_alt | exact _root_.GlobalTheory.RowTriple.Lay.EigCopy.eigenvalues_at_member_tripleLayer_alt | (intros; apply _root_.GlobalTheory.RowTriple.Lay.EigCopy.eigenvalues_at_member_tripleLayer_alt <;> assumption)
end
end
