module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsDefs
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsHyp
public import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalFiniteness.VanishAll
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.Bridge
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.MemDecompositionSubgroupIff
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsHypOfCmp
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsShaFinal
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.PTN

theorem locHyp_holds : LocHyp := PositivityTheory.PTNLoc.locHyp

theorem poitouTateNormalised_of_ptfs (hfs : PtfsHyp) (hvan : VanishAll) :
    PoitouTateNormalised :=
  poitouTateNormalised_of hfs locHyp_holds hvan

theorem poitouTateNormalised_of_cmp (hN : PositivityTheory.Lit1.PTN.NineCmpFS) (hS : PositivityTheory.Lit1.PTN.ShaCmpFS) :
    PoitouTateNormalised :=
  poitouTateNormalised_of_ptfs (PositivityTheory.Lit1.PTN.ptfsHyp_of_cmp hN hS) PositivityTheory.Lit1.GFVanish.vanishAll

theorem poitouTateNormalised_of_nine (hN : PositivityTheory.Lit1.PTN.NineCmpFS) : PoitouTateNormalised :=
  poitouTateNormalised_of_cmp hN PositivityTheory.Lit1.PTN.shaCmpFS'

end PositivityTheory.PTN
