module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictCapFBijective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp

namespace GlobalTheory.CechCmp

theorem cechOneCochainToPosetCochain_coboundary_exists : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R] (s : X ⟶ Sp R)
    (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)),
    ∀ c : GlobalTheory.KS.C1 U, IsCob U c → ∃ g, d0 (capF s U hU hinf) g = toPos s U hU hinf c := by
  intro I _ X R _ s U hU hinf c hc
  obtain ⟨b, hb⟩ := hc
  refine ⟨fun T => (cv s U hU hinf T).symm (rsT (b T.unop.pt) (cap U T.unop)), ?_⟩
  funext T T' φ
  apply (cv s U hU hinf T').injective
  have hTT' : cap U T'.unop ≤ cap U T.unop := cap_mono U (leOfHom φ.unop)
  have hp : cap U T.unop ≤ U T.unop.pt := cap_le U T.unop.pt_mem
  have hp' : cap U T'.unop ≤ U T'.unop.pt := cap_le U T'.unop.pt_mem
  have hle : cap U T'.unop ≤ U T.unop.pt ⊓ U T'.unop.pt := le_inf (hTT'.trans hp) hp'
  rw [amitsur_d0_apply, map_sub, cv_mp, cv_toPos, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, hb,
    GlobalTheory.KS.rsT_sub, GlobalTheory.KS.rsT_rsT inf_le_right hle, GlobalTheory.KS.rsT_rsT inf_le_left hle, GlobalTheory.KS.rsT_rsT hp hTT']

end GlobalTheory.CechCmp
