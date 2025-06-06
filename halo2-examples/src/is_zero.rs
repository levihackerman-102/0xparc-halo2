use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::*,
    dev::{MockProver, VerifyFailure},
    pasta::Fp,
    plonk::*,
    poly::Rotation,
};
use std::marker::PhantomData;
#[derive(Clone, Debug)]

pub struct IsZeroConfig<F> {
    pub value_inv: Column<Advice>, // value invert = 1/value
    pub is_zero_expr: Expression<F>, // if value = 0, then is_zero_expr = 1, else is_zero_expr = 0
    // We can use this is_zero_expr as a selector to trigger certain actions for example!
}

impl<F: FieldExt> IsZeroConfig<F> {
    pub fn expr(&self) -> Expression<F> {
        self.is_zero_expr.clone()
    }
}

pub struct IsZeroChip<F: FieldExt> {
    config: IsZeroConfig<F>,
}

impl<F: FieldExt> IsZeroChip<F> {
    pub fn construct(config: IsZeroConfig<F>) -> Self {
        IsZeroChip { config }
    }

    // q_enable is a selector to enable the gate. q_enable is a closure
    // value is the value to be checked. Value is a closure
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: impl FnOnce(&mut VirtualCells<'_, F>) -> Expression<F>,
        value: impl FnOnce(&mut VirtualCells<'_, F>) -> Expression<F>,
        value_inv: Column<Advice>,
    ) -> IsZeroConfig<F> {
        let mut is_zero_expr = Expression::Constant(F::zero());

        meta.create_gate("is_zero", |meta| {
            //
            // valid | value |  value_inv |  1 - value * value_inv | value * (1 - value* value_inv)
            // ------+-------+------------+------------------------+-------------------------------
            //  yes  |   x   |    1/x     |         0              |  0
            //  no   |   x   |    0       |         1              |  x
            //  yes  |   0   |    0       |         1              |  0
            //  yes  |   0   |    y       |         1              |  0

            // let's first get the value expression here from the lambda function
            let value = value(meta);
            let q_enable = q_enable(meta);
            // query value_inv from the advise colums
            let value_inv = meta.query_advice(value_inv, Rotation::cur());

            // This is the expression assignement for is_zero_expr
            is_zero_expr = Expression::Constant(F::one()) - value.clone() * value_inv;

            // there's a problem here. For example if we have a value x and a malicious prover add 0 to value_inv
            // then the prover can make the is_zero_expr = 1 - x * 0 = 1 - 0 = 1 which shouldn't be valid!
            // So we need to add a constraint to avoid that
            vec![q_enable * value * is_zero_expr.clone()]
        });

        IsZeroConfig {
            value_inv,
            is_zero_expr,
        }
    }

    // The assignment function takes the actual value, generate the inverse of that and assign it to the advice column
    pub fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        value: Value<F>,
    ) -> Result<(), Error> {
        let value_inv = value.map(|value| value.invert().unwrap_or(F::zero()));
        region.assign_advice(|| "value inv", self.config.value_inv, offset, || value_inv)?;
        Ok(())
    }
}

#[derive(Default)]
struct TestCircuit<F: FieldExt> {
    pub values: Vec<Value<F>>, // Test values to check
    _marker: PhantomData<F>,
}

#[derive(Clone, Debug)]
struct TestConfig<F: FieldExt> {
    pub advice: Column<Advice>,
    pub selector: Selector,
    pub is_zero_config: IsZeroConfig<F>,
}

impl<F: FieldExt> Circuit<F> for TestCircuit<F> {
    type Config = TestConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let advice = meta.advice_column();
        let selector = meta.selector();
        let value_inv = meta.advice_column();

        // Enable equality constraints for advice columns
        meta.enable_equality(advice);
        meta.enable_equality(value_inv);

        // Configure the IsZero chip
        let is_zero_config = IsZeroChip::configure(
            meta,
            |meta| meta.query_selector(selector), // q_enable
            |meta| meta.query_advice(advice, Rotation::cur()), // value
            value_inv,
        );

        TestConfig {
            advice,
            selector,
            is_zero_config,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let is_zero_chip = IsZeroChip::construct(config.is_zero_config);

        layouter.assign_region(
            || "test is_zero",
            |mut region| {
                for (i, &value) in self.values.iter().enumerate() {
                    // Enable the selector for this row
                    config.selector.enable(&mut region, i)?;

                    // Assign the test value
                    region.assign_advice(|| "value", config.advice, i, || value)?;

                    // Use the IsZero chip to assign the inverse
                    is_zero_chip.assign(&mut region, i, value)?;
                }
                Ok(())
            },
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_zero_with_various_values() {
        // Test values: zero, non-zero positive, non-zero negative
        let test_values = vec![
            Value::known(Fp::zero()),      // 0
            Value::known(Fp::one()),       // 1
            Value::known(Fp::from(42)),    // 42
            Value::known(-Fp::one()),      // -1
            Value::known(Fp::from(100)),   // 100
        ];

        let circuit = TestCircuit {
            values: test_values,
            _marker: PhantomData,
        };

        // Use MockProver to test the circuit
        let k = 4; // Circuit size (2^k rows)
        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        
        // This should pass if the circuit is correct
        assert_eq!(prover.verify(), Ok(()));
        
        println!("✅ All test values passed!");
    }

    // #[test]  
    // fn test_is_zero_should_fail_with_invalid_inverse() {
    //     // This test demonstrates what happens with invalid witness data
    //     // We'll create a custom circuit that tries to cheat
        
    //     #[derive(Default)]
    //     struct CheatCircuit<F: FieldExt> {
    //         _marker: PhantomData<F>,
    //     }

    //     impl<F: FieldExt> Circuit<F> for CheatCircuit<F> {
    //         type Config = TestConfig<F>;
    //         type FloorPlanner = SimpleFloorPlanner;

    //         fn without_witnesses(&self) -> Self {
    //             Self::default()
    //         }

    //         fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
    //             let advice = meta.advice_column();
    //             let selector = meta.selector();
    //             let value_inv = meta.advice_column();

    //             meta.enable_equality(advice);
    //             meta.enable_equality(value_inv);

    //             let is_zero_config = IsZeroChip::configure(
    //                 meta,
    //                 |meta| meta.query_selector(selector),
    //                 |meta| meta.query_advice(advice, Rotation::cur()),
    //                 value_inv,
    //             );

    //             TestConfig {
    //                 advice,
    //                 selector,
    //                 is_zero_config,
    //             }
    //         }

    //         fn synthesize(
    //             &self,
    //             config: Self::Config,
    //             mut layouter: impl Layouter<F>,
    //         ) -> Result<(), Error> {
    //             layouter.assign_region(
    //                 || "cheat test",
    //                 |mut region| {
    //                     config.selector.enable(&mut region, 0)?;
                        
    //                     // Assign non-zero value
    //                     region.assign_advice(|| "value", config.advice, 0, || Value::known(Fp::from(5)))?;
                        
    //                     // But assign zero as inverse (this should make the circuit fail)
    //                     region.assign_advice(|| "value_inv", config.is_zero_config.value_inv, 0, || Value::known(Fp::zero()))?;
                        
    //                     Ok(())
    //                 },
    //             )
    //         }
    //     }

    //     let cheat_circuit = CheatCircuit { _marker: PhantomData };
    //     let k = 4;
    //     let prover = MockProver::run(k, &cheat_circuit, vec![]).unwrap();
        
    //     // This should fail because we're cheating
    //     assert!(prover.verify().is_err());
    //     println!("✅ Cheating attempt correctly failed!");
    // }

    // #[test]
    // fn test_is_zero_expressions() {
    //     // Test that demonstrates how to check the is_zero expressions
    //     let test_values = vec![
    //         (Fp::zero(), true),       // 0 should give is_zero = true
    //         (Fp::one(), false),       // 1 should give is_zero = false  
    //         (Fp::from(42), false),    // 42 should give is_zero = false
    //     ];

    //     for (value, expected_is_zero) in test_values {
    //         // Manually compute what is_zero_expr should be
    //         let value_inv = if value == Fp::zero() {
    //             Fp::zero()
    //         } else {
    //             value.invert().unwrap()
    //         };
            
    //         let is_zero_expr = Fp::one() - value * value_inv;
    //         let is_zero_bool = is_zero_expr == Fp::one();
            
    //         assert_eq!(is_zero_bool, expected_is_zero, 
    //             "Value: {:?}, Expected is_zero: {}, Got: {}", 
    //             value, expected_is_zero, is_zero_bool);
    //     }
        
    //     println!("✅ Expression logic verified!");
    // }
}

// Helper function to run tests easily
pub fn run_is_zero_tests() {
    println!("Running IsZero chip tests...\n");
    
    // Test 1: Basic functionality
    let test_values = vec![
        Value::known(Fp::zero()),
        Value::known(Fp::one()), 
        Value::known(Fp::from(42)),
        Value::known(-Fp::one()),
    ];

    let circuit = TestCircuit {
        values: test_values,
        _marker: PhantomData,
    };

    let k = 4;
    match MockProver::run(k, &circuit, vec![]) {
        Ok(prover) => {
            match prover.verify() {
                Ok(()) => println!("✅ Basic test passed!"),
                Err(e) => println!("❌ Basic test failed: {:?}", e),
            }
        }
        Err(e) => println!("❌ Failed to run prover: {:?}", e),
    }
}
