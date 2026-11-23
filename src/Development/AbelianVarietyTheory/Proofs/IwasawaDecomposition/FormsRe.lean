module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RedivisionStructureEq
public import Formalism.LocalToGlobal.HermitianForms.TiedSym
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

noncomputable section

namespace GlobalTheory.Mem.SRe.ColRe

open Formalism.BasicNotions Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.SRe NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (Z : New D)



def formsRe {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (T : FormsTiedSym D u Ch chOf) :
    FormsTiedSym (reD D Z) u Ch chOf :=
  { T with
    atT := { T.atT with }
    cls := fun i hi h => { T.cls i hi h with }
    val := fun i hi h => { T.val i hi h with }
    lv := fun i hi => { T.lv i hi with }
    ch := fun i h1 h2 β => { T.ch i h1 h2 β with }
    valC := fun i h1 h2 => { T.valC i h1 h2 with }
    dilC := fun i h1 h2 => { T.dilC i h1 h2 with }
    lvC := fun i h1 h2 => { T.lvC i h1 h2 with }
    clsP := { T.clsP with }
    valP := { T.valP with }
    til := { T.til with }
    tilAd := { T.tilAd with } }

end GlobalTheory.Mem.SRe.ColRe

end
