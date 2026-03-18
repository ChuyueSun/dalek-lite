            field_element_from_bytes(&result.0) == 1,
            (result.0[31] >> 7) == 0,
    {
        CompressedEdwardsY::identity()
    }
}

impl CompressedEdwardsY {
    /// Construct a `CompressedEdwardsY` from a slice of bytes.
    ///
    /// # Errors
    ///
    /// Returns [`TryFromSliceError`] if the input `bytes` slice does not have
    /// a length of 32.
    pub fn from_slice(bytes: &[u8]) -> (result: Result<CompressedEdwardsY, TryFromSliceError>)
        ensures
            bytes@.len() == 32 ==> matches!(result, Ok(_)),
            bytes@.len() != 32 ==> matches!(result, Err(_)),
            match result {
                Ok(point) => point.0@ == bytes@,
                Err(_) => true,
            },
    {
        // ORIGINAL CODE: bytes.try_into().map(CompressedEdwardsY)
        // Verus does not support try_into and map
        // We use external wrapper functions with core_assumes for these functions.
        let arr_result = try_into_32_bytes_array(bytes);
        let result = compressed_edwards_y_from_array_result(arr_result);

        proof {
            // WORKS AUTOMATICALLY
