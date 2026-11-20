

#include "ClientHello.h"

#include "EverParse.h"

static inline uint64_t
ValidateExtension(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Validating field ext_type */
  /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
  BOOLEAN hasBytes0 = (InputLength - StartPosition) >= 2ULL;
  uint64_t positionAfterExtension;
  if (hasBytes0)
  {
    positionAfterExtension = StartPosition + 2ULL;
  }
  else
  {
    positionAfterExtension =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t res0;
  if (EverParseIsSuccess(positionAfterExtension))
  {
    res0 = positionAfterExtension;
  }
  else
  {
    ErrorHandlerFn("_Extension",
      "ext_type",
      EverParseErrorReasonOfResult(positionAfterExtension),
      EverParseGetValidatorErrorKind(positionAfterExtension),
      Ctxt,
      Input,
      StartPosition);
    res0 = positionAfterExtension;
  }
  uint64_t positionAfterextType = res0;
  if (EverParseIsError(positionAfterextType))
  {
    return positionAfterextType;
  }
  /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
  BOOLEAN hasBytes1 = (InputLength - positionAfterextType) >= 2ULL;
  uint64_t positionAfterExtension0;
  if (hasBytes1)
  {
    positionAfterExtension0 = positionAfterextType + 2ULL;
  }
  else
  {
    positionAfterExtension0 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterextType);
  }
  uint64_t positionAfterextLen;
  if (EverParseIsSuccess(positionAfterExtension0))
  {
    positionAfterextLen = positionAfterExtension0;
  }
  else
  {
    ErrorHandlerFn("_Extension",
      "ext_len",
      EverParseErrorReasonOfResult(positionAfterExtension0),
      EverParseGetValidatorErrorKind(positionAfterExtension0),
      Ctxt,
      Input,
      positionAfterextType);
    positionAfterextLen = positionAfterExtension0;
  }
  if (EverParseIsError(positionAfterextLen))
  {
    return positionAfterextLen;
  }
  uint16_t extLen = Load16Be(Input + (uint32_t)positionAfterextType);
  /* Validating field ext_data */
  BOOLEAN hasBytes = (InputLength - positionAfterextLen) >= (uint64_t)(uint32_t)extLen;
  uint64_t res;
  if (hasBytes)
  {
    res = positionAfterextLen + (uint64_t)(uint32_t)extLen;
  }
  else
  {
    res =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterextLen);
  }
  uint64_t positionAfterExtension1 = res;
  if (EverParseIsSuccess(positionAfterExtension1))
  {
    return positionAfterExtension1;
  }
  ErrorHandlerFn("_Extension",
    "ext_data",
    EverParseErrorReasonOfResult(positionAfterExtension1),
    EverParseGetValidatorErrorKind(positionAfterExtension1),
    Ctxt,
    Input,
    positionAfterextLen);
  return positionAfterExtension1;
}

uint64_t
ClientHelloValidateClientHelloBody(
  uint8_t *Ctxt,
  EVERPARSE_ERROR_HANDLER ErrorHandlerFn,
  uint8_t *Input,
  uint64_t InputLength,
  uint64_t StartPosition
)
{
  /* Validating field legacy_version */
  /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
  BOOLEAN hasBytes0 = (InputLength - StartPosition) >= 2ULL;
  uint64_t positionAfterClientHelloBody;
  if (hasBytes0)
  {
    positionAfterClientHelloBody = StartPosition + 2ULL;
  }
  else
  {
    positionAfterClientHelloBody =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t res0;
  if (EverParseIsSuccess(positionAfterClientHelloBody))
  {
    res0 = positionAfterClientHelloBody;
  }
  else
  {
    ErrorHandlerFn("_ClientHelloBody",
      "legacy_version",
      EverParseErrorReasonOfResult(positionAfterClientHelloBody),
      EverParseGetValidatorErrorKind(positionAfterClientHelloBody),
      Ctxt,
      Input,
      StartPosition);
    res0 = positionAfterClientHelloBody;
  }
  uint64_t positionAfterlegacyVersion = res0;
  if (EverParseIsError(positionAfterlegacyVersion))
  {
    return positionAfterlegacyVersion;
  }
  /* Validating field random */
  BOOLEAN hasBytes1 = (InputLength - positionAfterlegacyVersion) >= (uint64_t)32U;
  uint64_t res1;
  if (hasBytes1)
  {
    res1 = positionAfterlegacyVersion + (uint64_t)32U;
  }
  else
  {
    res1 =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterlegacyVersion);
  }
  uint64_t positionAfterClientHelloBody0 = res1;
  uint64_t positionAfterrandom;
  if (EverParseIsSuccess(positionAfterClientHelloBody0))
  {
    positionAfterrandom = positionAfterClientHelloBody0;
  }
  else
  {
    ErrorHandlerFn("_ClientHelloBody",
      "random",
      EverParseErrorReasonOfResult(positionAfterClientHelloBody0),
      EverParseGetValidatorErrorKind(positionAfterClientHelloBody0),
      Ctxt,
      Input,
      positionAfterlegacyVersion);
    positionAfterrandom = positionAfterClientHelloBody0;
  }
  if (EverParseIsError(positionAfterrandom))
  {
    return positionAfterrandom;
  }
  /* Checking that we have enough space for a UINT8, i.e., 1 byte */
  BOOLEAN hasBytes2 = (InputLength - positionAfterrandom) >= 1ULL;
  uint64_t positionAftersessionIdLen;
  if (hasBytes2)
  {
    positionAftersessionIdLen = positionAfterrandom + 1ULL;
  }
  else
  {
    positionAftersessionIdLen =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterrandom);
  }
  uint64_t positionAfterClientHelloBody1;
  if (EverParseIsError(positionAftersessionIdLen))
  {
    positionAfterClientHelloBody1 = positionAftersessionIdLen;
  }
  else
  {
    uint8_t sessionIdLen = Input[(uint32_t)positionAfterrandom];
    BOOLEAN sessionIdLenConstraintIsOk = sessionIdLen <= 32U;
    uint64_t
    positionAftersessionIdLen1 =
      EverParseCheckConstraintOk(sessionIdLenConstraintIsOk,
        positionAftersessionIdLen);
    if (EverParseIsError(positionAftersessionIdLen1))
    {
      positionAfterClientHelloBody1 = positionAftersessionIdLen1;
    }
    else
    {
      /* Validating field session_id */
      BOOLEAN
      hasBytes3 = (InputLength - positionAftersessionIdLen1) >= (uint64_t)(uint32_t)sessionIdLen;
      uint64_t res2;
      if (hasBytes3)
      {
        res2 = positionAftersessionIdLen1 + (uint64_t)(uint32_t)sessionIdLen;
      }
      else
      {
        res2 =
          EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
            positionAftersessionIdLen1);
      }
      uint64_t positionAfterClientHelloBody2 = res2;
      uint64_t positionAftersessionId;
      if (EverParseIsSuccess(positionAfterClientHelloBody2))
      {
        positionAftersessionId = positionAfterClientHelloBody2;
      }
      else
      {
        ErrorHandlerFn("_ClientHelloBody",
          "session_id",
          EverParseErrorReasonOfResult(positionAfterClientHelloBody2),
          EverParseGetValidatorErrorKind(positionAfterClientHelloBody2),
          Ctxt,
          Input,
          positionAftersessionIdLen1);
        positionAftersessionId = positionAfterClientHelloBody2;
      }
      if (EverParseIsError(positionAftersessionId))
      {
        positionAfterClientHelloBody1 = positionAftersessionId;
      }
      else
      {
        /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
        BOOLEAN hasBytes4 = (InputLength - positionAftersessionId) >= 2ULL;
        uint64_t positionAftercipherSuitesLen;
        if (hasBytes4)
        {
          positionAftercipherSuitesLen = positionAftersessionId + 2ULL;
        }
        else
        {
          positionAftercipherSuitesLen =
            EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
              positionAftersessionId);
        }
        uint64_t positionAfterClientHelloBody3;
        if (EverParseIsError(positionAftercipherSuitesLen))
        {
          positionAfterClientHelloBody3 = positionAftercipherSuitesLen;
        }
        else
        {
          uint16_t cipherSuitesLen = Load16Be(Input + (uint32_t)positionAftersessionId);
          BOOLEAN
          cipherSuitesLenConstraintIsOk =
            cipherSuitesLen >= (uint16_t)2U &&
              ((uint32_t)cipherSuitesLen % (uint32_t)(uint16_t)2U & 0xFFFFU) ==
                (uint32_t)(uint16_t)0U;
          uint64_t
          positionAftercipherSuitesLen1 =
            EverParseCheckConstraintOk(cipherSuitesLenConstraintIsOk,
              positionAftercipherSuitesLen);
          if (EverParseIsError(positionAftercipherSuitesLen1))
          {
            positionAfterClientHelloBody3 = positionAftercipherSuitesLen1;
          }
          else
          {
            /* Validating field cipher_suites */
            BOOLEAN
            hasBytes5 =
              (InputLength - positionAftercipherSuitesLen1) >= (uint64_t)(uint32_t)cipherSuitesLen;
            uint64_t res3;
            if (hasBytes5)
            {
              res3 = positionAftercipherSuitesLen1 + (uint64_t)(uint32_t)cipherSuitesLen;
            }
            else
            {
              res3 =
                EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                  positionAftercipherSuitesLen1);
            }
            uint64_t positionAfterClientHelloBody4 = res3;
            uint64_t positionAftercipherSuites;
            if (EverParseIsSuccess(positionAfterClientHelloBody4))
            {
              positionAftercipherSuites = positionAfterClientHelloBody4;
            }
            else
            {
              ErrorHandlerFn("_ClientHelloBody",
                "cipher_suites",
                EverParseErrorReasonOfResult(positionAfterClientHelloBody4),
                EverParseGetValidatorErrorKind(positionAfterClientHelloBody4),
                Ctxt,
                Input,
                positionAftercipherSuitesLen1);
              positionAftercipherSuites = positionAfterClientHelloBody4;
            }
            if (EverParseIsError(positionAftercipherSuites))
            {
              positionAfterClientHelloBody3 = positionAftercipherSuites;
            }
            else
            {
              /* Checking that we have enough space for a UINT8, i.e., 1 byte */
              BOOLEAN hasBytes6 = (InputLength - positionAftercipherSuites) >= 1ULL;
              uint64_t positionAftercompressionLen;
              if (hasBytes6)
              {
                positionAftercompressionLen = positionAftercipherSuites + 1ULL;
              }
              else
              {
                positionAftercompressionLen =
                  EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                    positionAftercipherSuites);
              }
              uint64_t positionAfterClientHelloBody5;
              if (EverParseIsError(positionAftercompressionLen))
              {
                positionAfterClientHelloBody5 = positionAftercompressionLen;
              }
              else
              {
                uint8_t compressionLen = Input[(uint32_t)positionAftercipherSuites];
                BOOLEAN compressionLenConstraintIsOk = compressionLen >= 1U;
                uint64_t
                positionAftercompressionLen1 =
                  EverParseCheckConstraintOk(compressionLenConstraintIsOk,
                    positionAftercompressionLen);
                if (EverParseIsError(positionAftercompressionLen1))
                {
                  positionAfterClientHelloBody5 = positionAftercompressionLen1;
                }
                else
                {
                  /* Validating field compression */
                  BOOLEAN
                  hasBytes7 =
                    (InputLength - positionAftercompressionLen1) >=
                      (uint64_t)(uint32_t)compressionLen;
                  uint64_t res;
                  if (hasBytes7)
                  {
                    res = positionAftercompressionLen1 + (uint64_t)(uint32_t)compressionLen;
                  }
                  else
                  {
                    res =
                      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                        positionAftercompressionLen1);
                  }
                  uint64_t positionAfterClientHelloBody6 = res;
                  uint64_t positionAftercompression;
                  if (EverParseIsSuccess(positionAfterClientHelloBody6))
                  {
                    positionAftercompression = positionAfterClientHelloBody6;
                  }
                  else
                  {
                    ErrorHandlerFn("_ClientHelloBody",
                      "compression",
                      EverParseErrorReasonOfResult(positionAfterClientHelloBody6),
                      EverParseGetValidatorErrorKind(positionAfterClientHelloBody6),
                      Ctxt,
                      Input,
                      positionAftercompressionLen1);
                    positionAftercompression = positionAfterClientHelloBody6;
                  }
                  if (EverParseIsError(positionAftercompression))
                  {
                    positionAfterClientHelloBody5 = positionAftercompression;
                  }
                  else
                  {
                    /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
                    BOOLEAN hasBytes = (InputLength - positionAftercompression) >= 2ULL;
                    uint64_t positionAfterClientHelloBody7;
                    if (hasBytes)
                    {
                      positionAfterClientHelloBody7 = positionAftercompression + 2ULL;
                    }
                    else
                    {
                      positionAfterClientHelloBody7 =
                        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                          positionAftercompression);
                    }
                    uint64_t positionAfterextensionsLen;
                    if (EverParseIsSuccess(positionAfterClientHelloBody7))
                    {
                      positionAfterextensionsLen = positionAfterClientHelloBody7;
                    }
                    else
                    {
                      ErrorHandlerFn("_ClientHelloBody",
                        "extensions_len",
                        EverParseErrorReasonOfResult(positionAfterClientHelloBody7),
                        EverParseGetValidatorErrorKind(positionAfterClientHelloBody7),
                        Ctxt,
                        Input,
                        positionAftercompression);
                      positionAfterextensionsLen = positionAfterClientHelloBody7;
                    }
                    if (EverParseIsError(positionAfterextensionsLen))
                    {
                      positionAfterClientHelloBody5 = positionAfterextensionsLen;
                    }
                    else
                    {
                      uint16_t extensionsLen = Load16Be(Input + (uint32_t)positionAftercompression);
                      /* Validating field extensions */
                      BOOLEAN
                      hasEnoughBytes =
                        (InputLength - positionAfterextensionsLen) >=
                          (uint64_t)(uint32_t)extensionsLen;
                      uint64_t positionAfterClientHelloBody8;
                      if (!hasEnoughBytes)
                      {
                        positionAfterClientHelloBody8 =
                          EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                            positionAfterextensionsLen);
                      }
                      else
                      {
                        uint8_t *truncatedInput = Input;
                        uint64_t
                        truncatedInputLength =
                          positionAfterextensionsLen + (uint64_t)(uint32_t)extensionsLen;
                        uint64_t result = positionAfterextensionsLen;
                        while (TRUE)
                        {
                          uint64_t position = result;
                          BOOLEAN ite;
                          if (!((truncatedInputLength - position) >= 1ULL))
                          {
                            ite = TRUE;
                          }
                          else
                          {
                            uint64_t
                            positionAfterClientHelloBody9 =
                              ValidateExtension(Ctxt,
                                ErrorHandlerFn,
                                truncatedInput,
                                truncatedInputLength,
                                position);
                            uint64_t result1;
                            if (EverParseIsSuccess(positionAfterClientHelloBody9))
                            {
                              result1 = positionAfterClientHelloBody9;
                            }
                            else
                            {
                              ErrorHandlerFn("_ClientHelloBody",
                                "extensions.element",
                                EverParseErrorReasonOfResult(positionAfterClientHelloBody9),
                                EverParseGetValidatorErrorKind(positionAfterClientHelloBody9),
                                Ctxt,
                                truncatedInput,
                                position);
                              result1 = positionAfterClientHelloBody9;
                            }
                            result = result1;
                            ite = EverParseIsError(result1);
                          }
                          if (ite)
                          {
                            break;
                          }
                        }
                        uint64_t res4 = result;
                        positionAfterClientHelloBody8 = res4;
                      }
                      if (EverParseIsSuccess(positionAfterClientHelloBody8))
                      {
                        positionAfterClientHelloBody5 = positionAfterClientHelloBody8;
                      }
                      else
                      {
                        ErrorHandlerFn("_ClientHelloBody",
                          "extensions",
                          EverParseErrorReasonOfResult(positionAfterClientHelloBody8),
                          EverParseGetValidatorErrorKind(positionAfterClientHelloBody8),
                          Ctxt,
                          Input,
                          positionAfterextensionsLen);
                        positionAfterClientHelloBody5 = positionAfterClientHelloBody8;
                      }
                    }
                  }
                }
              }
              if (EverParseIsSuccess(positionAfterClientHelloBody5))
              {
                positionAfterClientHelloBody3 = positionAfterClientHelloBody5;
              }
              else
              {
                ErrorHandlerFn("_ClientHelloBody",
                  "compression_len",
                  EverParseErrorReasonOfResult(positionAfterClientHelloBody5),
                  EverParseGetValidatorErrorKind(positionAfterClientHelloBody5),
                  Ctxt,
                  Input,
                  positionAftercipherSuites);
                positionAfterClientHelloBody3 = positionAfterClientHelloBody5;
              }
            }
          }
        }
        if (EverParseIsSuccess(positionAfterClientHelloBody3))
        {
          positionAfterClientHelloBody1 = positionAfterClientHelloBody3;
        }
        else
        {
          ErrorHandlerFn("_ClientHelloBody",
            "cipher_suites_len",
            EverParseErrorReasonOfResult(positionAfterClientHelloBody3),
            EverParseGetValidatorErrorKind(positionAfterClientHelloBody3),
            Ctxt,
            Input,
            positionAftersessionId);
          positionAfterClientHelloBody1 = positionAfterClientHelloBody3;
        }
      }
    }
  }
  if (EverParseIsSuccess(positionAfterClientHelloBody1))
  {
    return positionAfterClientHelloBody1;
  }
  ErrorHandlerFn("_ClientHelloBody",
    "session_id_len",
    EverParseErrorReasonOfResult(positionAfterClientHelloBody1),
    EverParseGetValidatorErrorKind(positionAfterClientHelloBody1),
    Ctxt,
    Input,
    positionAfterrandom);
  return positionAfterClientHelloBody1;
}

