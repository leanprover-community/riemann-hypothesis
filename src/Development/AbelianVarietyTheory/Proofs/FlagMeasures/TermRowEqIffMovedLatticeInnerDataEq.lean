module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DoubleCosetTermsSameInnerLatticesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IdentificationCompatIffLocalGraphsStatement
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IotaDictOut
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

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.DatEq

theorem row_eq_iff_datOf_eq : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (t : TauC Y u u') n m, t.lam = t₀.lam → t.lam' = t₀.lam' → n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → ((Y.tO u u').rowOf t = (Y.tO u u').rowOf t₀ ↔ G.datOf (c.lat (ρ * n) t.lam) = G.datOf (c.lat ρ t₀.lam)) := by
  intro D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv t n m hl hl' hnm
  have hA := GlobalTheory.T.doubleCoset_terms_same_innerLattices D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv t n m hl hl' hnm
  have hI := GlobalTheory.T.identificationCompat_iff_localGraphs D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv t n m hl hl' hnm
  have hD := Formalism.L2.SG.Pf.iotaDictAllC_holds D X Y u u' t₀ t hl.symm hl'.symm
  have hrow : ((Y.tO u u').rowOf t = (Y.tO u u').rowOf t₀) ↔
      iotaOf Y.TR (Y.cs u) (Y.cs u') t₀ = iotaOf Y.TR (Y.cs u) (Y.cs u') t := by
    show ((⟨t.lam, t.mem⟩, ⟨t.lam', t.mem'⟩, iotaOf Y.TR (Y.cs u) (Y.cs u') t) : Rw _ _ Y.TR) =
        (⟨t₀.lam, t₀.mem⟩, ⟨t₀.lam', t₀.mem'⟩, iotaOf Y.TR (Y.cs u) (Y.cs u') t₀) ↔ _
    constructor
    · intro h
      exact (congrArg (fun r => r.2.2) h).symm
    · intro h
      rw [h]
      ext <;> simp [hl, hl']
  rw [hrow, hD, hI]
  constructor
  · intro h
    funext p
    exact Prod.ext (hA p).1 (Prod.ext (hA p).2 (h p))
  · intro h p
    exact congrArg (fun d => (d p).2.2) h

end GlobalTheory.HL.DatEq
