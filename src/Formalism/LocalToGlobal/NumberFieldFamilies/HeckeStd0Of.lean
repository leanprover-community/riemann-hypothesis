module

public import Formalism.LocalToGlobal.NumberFieldFamilies.NPartCNd
public import Formalism.LocalToGlobal.NumberFieldFamilies.IsLocalizedOfSpan
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Module Polynomial

namespace Formalism.L2.Fam.NPC.LatticeFinitenessFree

open Formalism.L2.Fam.NPC



variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (B : LocBase0 H what₂)

def latJ (j : ℕ) (w : what₂.places.Pl) : Set (what₂.MtL (what₂.muTw w) j) :=
  {x | what₂.jMt (what₂.muTw w) j x ∈ (what₂.MtLat (what₂.muTw w) j).gen}

variable {B}

theorem span_latJ (j : ℕ) (w : what₂.places.Pl) : Submodule.span what₂.LL (latJ j w) = ⊤ := by
  have hb := what₂.jMt_basis (what₂.muTw w) j (Module.Free.chooseBasis what₂.LL _)
  refine span_top_of_image what₂.embLL (what₂.jMt (what₂.muTw w) j) _ hb.1 hb.2 _ ?_
  have h := (what₂.MtLat (what₂.muTw w) j).span_top
  refine le_antisymm le_top (h ▸ Submodule.span_mono fun v hv => ?_)
  obtain ⟨x, rfl⟩ := what₂.MtLat_sub _ _ v hv
  exact ⟨x, hv, rfl⟩

theorem span_iV (j : ℕ) (w : what₂.places.Pl) :
    Submodule.span (FractionRing (B.Oc j w)) (B.iV j w '' latJ j w) = ⊤ :=
  span_image_top (B.ec j w) (B.iV j w) (Module.Free.chooseBasis what₂.LL _) (B.iV_basis j w _).2 _ (span_latJ j w)

end Formalism.L2.Fam.NPC.LatticeFinitenessFree
