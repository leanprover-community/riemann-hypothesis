module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.DescUse
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.DescWeak
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.DifferentiableAtOm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.PlacesOverFinite.LinkedEndEOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
import Development.AutomorphicArithmetic.CharacterBoxes.ExistsPageN

@[expose] public section

open Formalism.GaloisCohomology UpperTheory.Top GlobalTheory.Mem.LiteralAutomorphy

namespace UpperTheory.V.Z.Sym.Top

open UpperTheory.V.Lit UpperTheory.V.W UpperTheory.V.HV UpperTheory.V.Z.Sym.Pl

theorem descUse_of_weak (h : Z.Desc.DescWeak) : Z.Desc.DescUse :=
  fun E _ _ _ hE p hp S hS h1 h2 n hn hn' π hr _ => h E hE p hp S hS h1 h2 n hn hn' π hr

end UpperTheory.V.Z.Sym.Top
