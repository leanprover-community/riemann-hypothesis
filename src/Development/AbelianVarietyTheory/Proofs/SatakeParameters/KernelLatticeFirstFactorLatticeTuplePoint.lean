module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePtOne
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatAdLocOf
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocSpCompanEq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocSpLatAdIsPt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MapApplyEqMulVec
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulDualSetLatAdMem
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsRowFrame
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
import Formalism.LocalToGlobal.InertKernelTheory.SecondKernelEntrywiseLastLevel
import Formalism.LocalToGlobal.InertKernelTheory.StatementInt
import Formalism.LocalToGlobal.KernelLattices.TopLawQ
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.NrmAMemAdForms

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.TwV.KerSp

theorem locSp_latK_isPt : ∀ {D : D7} {i : ℕ} {hi : i ≤ D.R.m} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T D.R.f bad) {p : ℕ} {G : GAtP p} (A : LocAt D.host.F D.host.E (D.R.N i) G) (a : 𝓞 D.host.E), (∃ co, IsOrthCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) co) → SplAlg A → LocInt A → LbAtB A lev.Lb → 0 < T → ∀ (c : G.comp) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)) (x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)), A.IsPt c g x.1 → ∀ v, IsUnit (T : G.P.W v) → locSp (G.P.W v) (A.iw v) (latK D.sp (gramN D i hi) a x.1 lev.Lb) = colSpan (G.P.W v) ((LinearMap.toMatrix' (stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi)).toLinearMap * A.B.1).map (A.iw v) * (castGL A.rk (G.P.Qq v) (g v) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) (G.P.Qq v))) := by
  intro D i hi T bad lev p G A a hco hS hI hB hT c g x hx v hTv
  have hLb : Formalism.L2.GlobalTheoryTheory.Comp.IsLat lev.Lb := ⟨lev.Lb_fin, lev.Lb_span⟩
  have hdual := GlobalTheory.smul_dualSet_latAd_mem D.sp (gramN D i hi) hco T lev.Lb hT hLb lev.Lb_dual x.1 x.2
  have hLA : LatAdLoc A lev.Lb := GlobalTheory.TwV.latAdLoc_of A lev.Lb hS hI lev.Lb_fin lev.Lb_span
  unfold Formalism.MainNotions.G.KAat.latK Formalism.L2.PairingIndexBounds.F.toStd
  rw [GlobalTheory.TwV.locSp_map, GlobalTheory.TwV.CompSp.locSp_compan_eq D.sp (G.P.W v) (G.P.Qq v) (A.iw v) (gramN D i hi) a T _ hTv hdual,
    GlobalTheory.TwV.SpanPt.locSp_latAd_isPt A lev.Lb hLA hB c g x.1 hx v, GlobalTheory.TwV.SpanPt.colSpan_map]
  rw [Matrix.map_mul, Matrix.mul_assoc]
  rfl

end GlobalTheory.TwV.KerSp
