module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.NilToPhiAlt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.LocFacts
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.SemistableModelSemistable
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.CardResOK
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.ExistsLin
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.LocTowerHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.NiceBc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

theorem UpperTheory.Gal.Int.Geo.geoSide_of :
    UpperTheory.Gal.crystallineComparison.Br.FinAll → CrystallineSemistableComparison.SmoothModelCrystalline → UpperTheory.Ru.crystallineComparison.GeoSide := by
  intro hFin hCr E Ω _ _ _ _ _ l _ H θ hN a ρ₀ hMat w hw n ϑ hCong P AI hT A hA O _ _ _ Bw hj
  obtain ⟨hD, hDV, hf, hnorm, hcard, C, hOnto, hCg⟩ :=
    UpperTheory.Ru.crystallineComparison.congBC E Ω l _ H θ w hw n ϑ hCong A hA O Bw hj
  obtain ⟨ρ₁, hM₁, hρ₁⟩ :=
    UpperTheory.Gal.Seam.locTower_holds l E ↥Bw.Kw.1 Ω _
      (UpperTheory.Gal.Seam.kOf Bw) Bw.j (fun _ => rfl) H hN _ θ a ρ₀ hMat
  obtain ⟨V, i₁, i₂, i₃, ρ, T, b, hcr, hann, hinj, hact, heig⟩ :=
    UpperTheory.Ru.crystallineComparison.geoLoc hFin hCr l P AI hT Bw.Kw _ hf hcard
      (UpperTheory.Gal.Int.Geo.bcAlong H (UpperTheory.Gal.Seam.kOf Bw)) θ
      (UpperTheory.Gal.Seam.niceBc _ _ (UpperTheory.Gal.Seam.kOf Bw) H hN) C hOnto n ϑ hCg a ρ₁ hM₁
  rw [hnorm]
  refine ⟨V, i₁, i₂, i₃, ρ, T, b, hcr, hann, hinj, fun g x => ?_, heig⟩
  have h := hact (Bw.e g) x
  rwa [hρ₁ (g : Ω ≃ₐ[E] Ω) _ fun y => Bw.e_comm g y] at h
