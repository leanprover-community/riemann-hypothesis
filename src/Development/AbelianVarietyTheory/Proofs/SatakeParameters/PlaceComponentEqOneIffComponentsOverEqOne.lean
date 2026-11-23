module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteAdeleFieldIdentificationEqBaseChangeRingEq
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
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.DIV
open scoped TensorProduct

namespace GlobalTheory.AfIsoPrV

theorem prV_eq_one_iff_afIso : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (z : AfE F E), Formalism.UG.prV (E := E) v z = 1 ↔ ∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) = v → GlobalTheory.Mem.Col2.afIso F E z P = 1 := by
  intro F E _ _ _ _ _ v z
  obtain ⟨ι, hι⟩ := GlobalTheory.AdeleBaseChange.exists_toAd F E
  let ι' : AfE F E ≃+* FiniteAdeleRing (𝓞 E) E :=
    RingEquiv.ofBijective ι ⟨GlobalTheory.AdeleBaseChange.map_injective hι, GlobalTheory.AdeleBaseChange.map_surjective hι⟩
  have hiso : GlobalTheory.TwU.IsAdIso ι' :=
    ⟨GlobalTheory.AdeleBaseChange.map_tmul_one hι,
      fun y => ⟨fun hy => GlobalTheory.AdeleBaseChange.map_mem_int hι hy,
        fun hy => GlobalTheory.AdeleBaseChange.mem_int_of_map hι hy⟩⟩
  have he : ι z = GlobalTheory.Mem.Col2.afIso F E z := GlobalTheory.isAdIso_eq_afIso F E ι' hiso z
  rw [GlobalTheory.AdeleBaseChange.prV_eq_one_iff hι, he]

end GlobalTheory.AfIsoPrV
