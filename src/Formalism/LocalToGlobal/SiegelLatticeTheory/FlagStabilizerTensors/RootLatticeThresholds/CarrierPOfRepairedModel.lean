module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierInputExistsBuilt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.SpectralTiesReal
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

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
open Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups

namespace Formalism.L2.SG.SpectralTiesReal

open Formalism.L2.SG.AdBridge Formalism.L2.SG.DataInst Formalism.L2.SG.RealObj

def CarrierSideBoundPositive (Cb : ℝ) : Prop :=
  ∀ C₆ Cc : ℝ, 0 < C₆ → ∃ CA₀ : ℝ, ∀ CA : ℝ, CA₀ ≤ CA → 1 ≤ CA →
    ∀ C0 CG CDel cT Cb' : ℝ, 1 ≤ C0 → 0 ≤ CG → 4 < CDel → 0 < cT → 0 < Cb' → 1 < cT * Cb' →
    ∃ k0 : ℕ, ∀ Cg cb Cw cTf CT C0f : ℝ, 0 < cb → 0 < cTf → ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (L : SizeData₂ D) (T : STies D) (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau)
      (τ : D.what₂.Tau) (Cp Th' : ℝ)
      (i0 i0' : ∀ _ : InfinitePlace T.X.B.I.F, Fin D.R.k) (νq : T.X.B.I.Ginf → Measure T.X.B.I.Ginf)
      (X0 : Fin (2 * D.R.rS + 2) → Fin T.X.B.I.n → T.X.B.I.E) (sd C Th : ℝ)
      {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
      (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂),
      Formalism.BasicNotions.Ties D → u ≠ u' → k0 ≤ (gOf D e).k → Formalism.MainNotions.S.Cnt.Hyp0 D L C' Cl Cg cb Cw cTf CT C0f →
      (∀ x : InfinitePlace D.host.E,
        InfinitePlace.mk ((T.X.B.I.φ (T.X.pl.symm (e x))).comp T.X.ιE.symm.toRingHom) = x) →
      J.SzHyp (gOf D e) CA C0 CG CDel cT Cb' L.sc.b Cp Th' (deOf D τ u) (deOf D τ u')
        (D.mem u).A.T (D.mem u').A.T (D.duS u) (D.duS u') (lOf D (deOf D τ u) (deOf D τ u')) →
      (∀ v, i0 v = i0' v) → PtRepExists T.X u u' 1 i0 i0' → NuQPin T.X u u' νq →
      Formalism.L2.SG.Pf.CarrierT.CarrierDataBound T.X u u' 1 i0 i0' (T.Y.FN u) (T.Y.FN u') νq
        (massDataY T.X T.hb T.Y u u' X0 T.ψ sd C Th vR Q i0 i0' νq).IntN CA (gOf D e) (deOf D τ u) (deOf D τ u')
        (lOf D (deOf D τ u) (deOf D τ u')) C₆ Cc Cb

end Formalism.L2.SG.SpectralTiesReal
