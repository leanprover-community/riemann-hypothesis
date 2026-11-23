module

public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
public import Formalism.LocalToGlobal.Columns.StdLatUnimodular
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualLatticeIsLatticeAndHermitianDual
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeExtensionAlongFieldEmbeddingDuals
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NabLeDelOfLocal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass

@[expose] public section

noncomputable section

namespace GlobalTheory.KerT

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker

theorem spread_lt_of_two_mul_lt {n p : ℕ} (hp : p.Prime) (lam : DomWeight n)
    (h : ∀ a b : Fin n, 2 * (lam.w a - lam.w b + (n : ℤ)) < (p : ℤ)) : lam.spread < p := by
  have hp0 := hp.pos
  unfold DomWeight.spread
  split_ifs with hn
  · have := h ⟨0, hn⟩ ⟨n - 1, by omega⟩
    omega
  · omega

theorem localization_delAtr_eq_localization_nabAtr : GlobalTheory.Published.InducedSimpleLowestAlcove →
    ∀ (X : Fields) (n p : ℕ) (lam : X.Tau → DomWeight n), p.Prime →
      (∀ τ (a b : Fin n), 2 * ((lam τ).w a - (lam τ).w b + (n : ℤ)) < (p : ℤ)) →
      ∀ w : HeightOneSpectrum (𝓞 X.K), ((p : ℕ) : 𝓞 X.K) ∈ w.asIdeal →
        ∀ L : Submodule (𝓞 X.E) (Sp X.E n), Submodule.IsFullLattice X.E L →
          localization₂ w.asIdeal (delAtr X.emb lam L) = localization₂ w.asIdeal (nabAtr X.emb lam L) := by
  intro h X n p lam hp hl w hw L hL
  refine le_antisymm ?_ ?_
  · rintro x ⟨s, hs, hx⟩
    exact ⟨s, hs, delLeNab X.K X.Tau n lam _ hx⟩
  · exact GlobalTheory.ColPeriod.WeylLoc.nabLeDel_of_local (GlobalTheory.Published.weylDualWeylLatticesAgree_of_lowest_alcove h) X.K X.Tau n lam _
      (fun τ => GlobalTheory.DualLat.isLattice_dualFr _ (GlobalTheory.TauLat.tauLatLattice X.E X.K X.Tau n X.emb τ L hL)) p w hp hw
      fun τ => spread_lt_of_two_mul_lt hp (lam τ) (hl τ)

end GlobalTheory.KerT
