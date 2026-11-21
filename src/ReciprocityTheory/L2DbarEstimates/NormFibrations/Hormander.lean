import ReciprocityTheory.L2DbarEstimates.NormFibrations.Imports
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.InhHasFDerivAtNormSq
import ReciprocityTheory.L2DbarEstimates.Mollifiers.Imports
import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.Imports
import ReciprocityTheory.L2DbarEstimates.MinimalSolutions.HilbertLemmas
import ReciprocityTheory.L2DbarEstimates.BasicIdentity.ImportsAlt
import ReciprocityTheory.L2DbarEstimates.HormanderEstimate.HStatementOf
import ReciprocityTheory.L2DbarEstimates.HormanderEstimate.Closed
import ReciprocityTheory.L2DbarEstimates.SkodaWeights.Imports
import ReciprocityTheory.L2DbarEstimates.LeviForms.Imports

universe u

namespace ReciprocityTheory.L2DbarEstimates

open MeasureTheory

theorem regMAll (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : F.RegMStatement n M :=
  F.regM n M C.reg (F.extend n M)

theorem hormander (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : HStatement n M :=
  F.hStatement_of n M (E.ap n M) (E.tStarIbp n M) (chain n M) C.reg
    (B.moll_graph (V n) volume ℝ) (B.moll_smooth (V n) volume) (B.moll_support (V n) volume)
    (B.kernel_std (V n) volume)

theorem skoda (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : SStatement n M :=
  H.skoda n M (fun p => hormander n (M × Fin p))
    (fun p => F.needBergmanClosed n (M × Fin p) (regMAll n (M × Fin p)))

theorem tw (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : TWStatement n M :=
  I.tw n M (hormander n M) (F.holoClosedNeed n M (regMAll n M))


theorem ma (n : ℕ) : MAStatement n :=
  I.ma n (I.maCof n)

theorem detMono (n : ℕ) : DetMonoStatement n :=
  I.maDet n

theorem inhabited (n : ℕ) : InhabitedStatement n :=
  etaleStein_nonempty n

end ReciprocityTheory.L2DbarEstimates
