module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdmissibleIntegralFrameOfLocalTerms
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

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_admissible_integralFrame_of_localTerms : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ n m, n ∈ NRat (lf D (X.Fu u)) → m ∈ NRat (lf D (X.Fu u')) → Formalism.HermitianLatticesTheory.gmap (n⁻¹ * t₀.lin * m) t₀.lam' = t₀.lam → (∃ d, G.IsTerm d (c.lat (ρ * n) t₀.lam)) → Formalism.L2.SG.TermDef.PD D t₀.lam (lf D (X.Fu u)) u' (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))) := by
  first | exact @GlobalTheory.HL.AdmFrame.exists_admissible_integralFrame_of_localTerms_alt | exact GlobalTheory.HL.AdmFrame.exists_admissible_integralFrame_of_localTerms_alt | (intros; apply GlobalTheory.HL.AdmFrame.exists_admissible_integralFrame_of_localTerms_alt <;> assumption)
