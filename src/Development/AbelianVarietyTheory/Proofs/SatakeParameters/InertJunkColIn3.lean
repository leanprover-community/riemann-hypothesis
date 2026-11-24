module

public import Formalism.LocalToGlobal.Divisibility.HeckeCSDICommTrRep
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodGeneric
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotGoodGenericSign
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

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef

namespace GlobalTheory.Hk3

theorem inertJunk_iff {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {m : ℕ}
    (A3 : FamIn3 K G Pl0 I0 (List ℕ) T m) :
    InertJunk A3 ↔
      ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨
          ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧
        ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨
          ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) :=
  ⟨fun h => ⟨fun t k => h.R t k.1 k.2, fun j t k => h.L j t k.1 k.2⟩,
    fun h => ⟨fun t Q s => h.1 t (Q, s), fun j t Q s => h.2 j t (Q, s)⟩⟩

theorem inertJunk_colIn3 {X : Col.Fields} {Pr : Col.Primes X} {R : Ranks} (W : Col.Wts X Pr.Word R) (Ch : Col.Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (hX : X.Ok)
    (v0 : InfinitePlace X.K) (TU : Finset (Tup X.F X.E X.K S))
    (Xg : Finset (Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))
    (xiVal : Tup X.F X.E X.K S → HeightOneSpectrum (𝓞 X.E) → X.Kˣ)
    (trIv : Fin R.m → (Col.LevOffI ∅ Pr.vGs S0 × List ℕ → X.K) → Col.LevOffI ∅ Pr.vGs S0 × List ℕ → X.K) :
    InertJunk (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv) :=
  FamModel.inertJunk_col W Ch sel hX v0 TU Xg S0 xiVal trIv

end GlobalTheory.Hk3
