module

public import Formalism.LocalToGlobal.HermitianForms.TiedTwSymAll
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

open Formalism.BasicNotions

namespace Formalism.L2.Rows

structure EMtTied (D : D7) (C : Formalism.L2.Forms.ColsTiedSym D) {cf : Formalism.L2.Host.CharFrame D} {nch : NChoice D}
    {tp : Formalism.L2.Host.TupTied D cf nch} {Tw : TwForms D} (tw : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes tp C Tw) : Prop where

  mu0 : ∀ (u : D.what₂.Word) (F G : (D.mem u).P.Mt),
    inner ℂ (D.eMt u F) (D.eMt u G) = (D.fm u).ipP ((C.forms u).jM G) ((C.forms u).jM F)

  tw : ∀ (u : D.what₂.Word) (μ : D.what₂.Tup), μ ≠ D.what₂.mu0 → ∀ (F G : (D.PTw u μ).Mt),
    inner ℂ (D.eMtTw u μ F) (D.eMtTw u μ G) = (Tw.fm u μ).ipP (tw.ptE.jM u μ G) (tw.ptE.jM u μ F)

end Formalism.L2.Rows

end
