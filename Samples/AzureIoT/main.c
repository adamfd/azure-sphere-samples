﻿/* Copyright (c) Microsoft Corporation. All rights reserved.
   Licensed under the MIT License. */

// This sample C application demonstrates how to interface Azure Sphere devices with Azure IoT
// services. Using the Azure IoT SDK C APIs, it shows how to:
// 1. Use Device Provisioning Service (DPS) to connect to Azure IoT Hub/Central with
// certificate-based authentication
// 2. Use X.509 Certificate Authority (CA) certificates to authenticate devices connecting directly
// to Azure IoT Hub
// 3. Use Device Twin to upload simulated temperature measurements, upload button press events and
// receive a desired LED state from Azure IoT Hub/Central
// 4. Use Direct Methods to receive a "Trigger Alarm" command from Azure IoT Hub/Central

// You will need to provide information in application manifest to use this application.
// If using DPS to connect, you must provide:
// 1. The Tenant ID obtained from 'azsphere tenant show-selected' (set in 'DeviceAuthentication')
// 2. The Azure DPS Global endpoint address 'global.azure-devices-provisioning.net'
//    (set in 'AllowedConnections')
// 3. The Azure IoT Hub Endpoint address(es) that DPS is configured to direct this device to (set in
// 'AllowedConnections')
// 4. Type of connection to use when connecting to the Azure IoT Hub (set in 'CmdArgs')
// 5. The Scope Id for the Device Provisioning Service - DPS (set in 'CmdArgs')
// If connecting directly to an Azure IoT Hub, you must provide:
// 1. The Tenant Id obtained from 'azsphere tenant
// show-selected' (set in 'DeviceAuthentication')
// 2. The Azure IoT Hub Endpoint address(es) (set in 'AllowedConnections')
// 3. Azure IoT Hub hostname (set in 'CmdArgs')
// 4. Device ID (set in 'CmdArgs' and must be in lowercase)
// 5. Type of connection to use when connecting to the Azure IoT Hub (set in 'CmdArgs')

#include <ctype.h>
#include <errno.h>
#include <getopt.h>
#include <signal.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <math.h>

// applibs_versions.h defines the API struct versions to use for applibs APIs.
#include "applibs_versions.h"
#include <applibs/eventloop.h>
#include <applibs/gpio.h>
#include <applibs/log.h>
#include <applibs/networking.h>
#include <applibs/i2c.h>

// Grove Temperature and Humidity Sensor
#include "../MT3620_Grove_Shield/MT3620_Grove_Shield_Library/Grove.h"
#include "../MT3620_Grove_Shield/MT3620_Grove_Shield_Library/Sensors/GroveTempHumiSHT31.h"


// The following #include imports a "sample appliance" definition. This app comes with multiple
// implementations of the sample appliance, each in a separate directory, which allow the code to
// run on different hardware.
//
// By default, this app targets hardware that follows the MT3620 Reference Development Board (RDB)
// specification, such as the MT3620 Dev Kit from Seeed Studio.
//
// To target different hardware, you'll need to update CMakeLists.txt. For example, to target the
// Avnet MT3620 Starter Kit, change the TARGET_DIRECTORY argument in the call to
// azsphere_target_hardware_definition to "HardwareDefinitions/avnet_mt3620_sk".
//
// See https://aka.ms/AzureSphereHardwareDefinitions for more details.
#include <hw/sample_appliance.h>

#include "eventloop_timer_utilities.h"
#include "parson.h" // Used to parse Device Twin messages.

// Azure IoT SDK
#include <iothub_client_core_common.h>
#include <iothub_device_client_ll.h>
#include <iothub_client_options.h>
#include <iothubtransportmqtt.h>
#include <iothub.h>
#include <azure_sphere_provisioning.h>
#include <iothub_security_factory.h>

/// <summary>
/// Exit codes for this application. These are used for the
/// application exit code. They must all be between zero and 255,
/// where zero is reserved for successful termination.
/// </summary>
typedef enum {
    ExitCode_Success = 0,

    ExitCode_TermHandler_SigTerm = 1,

    ExitCode_Main_EventLoopFail = 2,

    ExitCode_ButtonTimer_Consume = 3,

    ExitCode_AzureTimer_Consume = 4,

    ExitCode_Init_EventLoop = 5,
    ExitCode_Init_MessageButton = 6,
    ExitCode_Init_OrientationButton = 7,
    ExitCode_Init_TwinStatusLed = 8,
    ExitCode_Init_TwinRLed = 21,
    ExitCode_Init_TwinGLed = 22,
    ExitCode_Init_TwinBLed = 23,
    ExitCode_Init_ButtonPollTimer = 9,
    ExitCode_Init_AzureTimer = 10,
    ExitCode_Init_AccelTimer = 16,
    ExitCode_Init_OpenMaster = 17,
    ExitCode_Init_SetBusSpeed = 18,
    ExitCode_Init_SetTimeout = 19,
    ExitCode_Init_SetDefaultTarget = 20,

    ExitCode_IsButtonPressed_GetValue = 11,

    ExitCode_Validate_ConnectionType = 12,
    ExitCode_Validate_ScopeId = 13,
    ExitCode_Validate_IotHubHostname = 14,
    ExitCode_Validate_DeviceId = 15,

    ExitCode_InterfaceConnectionStatus_Failed = 16,

        ExitCode_ReadWhoAmI_WriteThenRead = 5,
    ExitCode_ReadWhoAmI_WriteThenReadCompare = 6,
    ExitCode_ReadWhoAmI_Write = 7,
    ExitCode_ReadWhoAmI_Read = 8,
    ExitCode_ReadWhoAmI_WriteReadCompare = 9,
    ExitCode_ReadWhoAmI_PosixWrite = 10,
    ExitCode_ReadWhoAmI_PosixRead = 11,
    ExitCode_ReadWhoAmI_PosixCompare = 12,

} ExitCode;

static volatile sig_atomic_t exitCode = ExitCode_Success;

/// <summary>
/// Connection types to use when connecting to the Azure IoT Hub.
/// </summary>
typedef enum {
    ConnectionType_NotDefined = 0,
    ConnectionType_DPS = 1,
    ConnectionType_Direct = 2
} ConnectionType;

/// <summary>
/// Authentication state of the client with respect to the Azure IoT Hub.
/// </summary>
typedef enum {
    /// <summary>Client is not authenticated by the Azure IoT Hub.</summary>
    IoTHubClientAuthenticationState_NotAuthenticated = 0,
    /// <summary>Client has initiated authentication to the Azure IoT Hub.</summary>
    IoTHubClientAuthenticationState_AuthenticationInitiated = 1,
    /// <summary>Client is authenticated by the Azure IoT Hub.</summary>
    IoTHubClientAuthenticationState_Authenticated = 2
} IoTHubClientAuthenticationState;

// Azure IoT definitions.
static char *scopeId = NULL;                                      // ScopeId for DPS.
static char *hubHostName = NULL;                                  // Azure IoT Hub Hostname.
static char *deviceId = NULL;                                     // Device ID must be in lowercase.
static ConnectionType connectionType = ConnectionType_NotDefined; // Type of connection to use.
static IoTHubClientAuthenticationState iotHubClientAuthenticationState =
    IoTHubClientAuthenticationState_NotAuthenticated; // Authentication state with respect to the
                                                      // IoT Hub.

static IOTHUB_DEVICE_CLIENT_LL_HANDLE iothubClientHandle = NULL;
static const int deviceIdForDaaCertUsage = 1; // A constant used to direct the IoT SDK to use
                                              // the DAA cert under the hood.
static const char NetworkInterface[] = "wlan0";

// Function declarations
static void SendEventCallback(IOTHUB_CLIENT_CONFIRMATION_RESULT result, void *context);
static void DeviceTwinCallback(DEVICE_TWIN_UPDATE_STATE updateState, const unsigned char *payload,
                               size_t payloadSize, void *userContextCallback);
static void TwinReportState(const char *jsonState);
static void ReportedStateCallback(int result, void *context);
static int DeviceMethodCallback(const char *methodName, const unsigned char *payload,
                                size_t payloadSize, unsigned char **response, size_t *responseSize,
                                void *userContextCallback);
static const char *GetReasonString(IOTHUB_CLIENT_CONNECTION_STATUS_REASON reason);
static const char *GetAzureSphereProvisioningResultString(
    AZURE_SPHERE_PROV_RETURN_VALUE provisioningResult);
static void SendTelemetry(const char *jsonMessage);
static void SetUpAzureIoTHubClient(void);
static void SendSimulatedTelemetry(void);
static void SendTempTelemetry(void);
static void SendGPIO1Telemetry(void);
static void SendGPIO2Telemetry(void);
static void SendGPIO3Telemetry(void);
static void ButtonPollTimerEventHandler(EventLoopTimer *timer);
static bool IsButtonPressed(int fd, GPIO_Value_Type *oldState);
static void AzureTimerEventHandler(EventLoopTimer *timer);
static ExitCode ValidateUserConfiguration(void);
static ExitCode ReadWhoAmI(void);
static void ParseCommandLineArguments(int argc, char *argv[]);
static bool SetUpAzureIoTHubClientWithDaa(void);
static bool SetUpAzureIoTHubClientWithDps(void);
static bool IsConnectionReadyToSendTelemetry(void);
static bool CheckTransferSize(const char *desc, size_t expectedBytes, ssize_t actualBytes);

// Initialization/Cleanup
static ExitCode InitPeripheralsAndHandlers(void);
static void CloseFdAndPrintError(int fd, const char *fdName);
static void ClosePeripheralsAndHandlers(void);

// File descriptors - initialized to invalid value
// Button
static int sendMessageButtonGpioFd = -1;
static int sendMessageGpio0Fd = -1;
static int sendMessageGpio1Fd = -1;
static int sendMessageGpio2Fd = -1;
static int sendMessageGpio3Fd = -1;
static int i2cFd = -1;
void *sht31;

// LED
static int deviceTwinStatusLedGpioFd = -1;
static int deviceTwinRLedGpioFd = -1;
static int deviceTwinGLedGpioFd = -1;
static int deviceTwinBLedGpioFd = -1;

// Timer / polling
static EventLoop *eventLoop = NULL;
static EventLoopTimer *buttonPollTimer = NULL;
static EventLoopTimer *azureTimer = NULL;

// Azure IoT poll periods
static const int AzureIoTDefaultPollPeriodSeconds = 2;        // poll azure iot every second
static const int AzureIoTPollPeriodsPerTelemetry = 10;         // only send telemetry 1/5 of polls
static const int AzureIoTMinReconnectPeriodSeconds = 60;      // back off when reconnecting
static const int AzureIoTMaxReconnectPeriodSeconds = 10 * 60; // back off limit

static int azureIoTPollPeriodSeconds = -1;
static int telemetryCount = 0;

// State variables
static GPIO_Value_Type sendMessageButtonState = GPIO_Value_High;
static bool statusLedOn = false;
static bool RLedOn = false;
static bool GLedOn = false;
static bool BLedOn = false;

// Usage text for command line arguments in application manifest.
static const char *cmdLineArgsUsageText =
    "DPS connection type: \" CmdArgs \": [\"--ConnectionType\", \"DPS\", \"--ScopeID\", "
    "\"<scope_id>\"]\n"
    "Direction connection type: \" CmdArgs \": [\"--ConnectionType\", \"Direct\", "
    "\"--Hostname\", \"<azureiothub_hostname>\", \"--DeviceID\", \"<device_id>\"]\n";

/// <summary>
///     Signal handler for termination requests. This handler must be async-signal-safe.
/// </summary>
static void TerminationHandler(int signalNumber)
{
    // Don't use Log_Debug here, as it is not guaranteed to be async-signal-safe.
    exitCode = ExitCode_TermHandler_SigTerm;
}

/// <summary>
///     Main entry point for this sample.
/// </summary>
int main(int argc, char *argv[])
{
    Log_Debug("Azure IoT Application starting.\n");

    bool isNetworkingReady = false;
    if ((Networking_IsNetworkingReady(&isNetworkingReady) == -1) || !isNetworkingReady) {
        Log_Debug("WARNING: Network is not ready. Device cannot connect until network is ready.\n");
    }

    ParseCommandLineArguments(argc, argv);

    exitCode = ValidateUserConfiguration();
    if (exitCode != ExitCode_Success) {
        return exitCode;
    }

    exitCode = InitPeripheralsAndHandlers();

    // Main loop
    while (exitCode == ExitCode_Success) {
        EventLoop_Run_Result result = EventLoop_Run(eventLoop, -1, true);
        // Continue if interrupted by signal, e.g. due to breakpoint being set.
        if (result == EventLoop_Run_Failed && errno != EINTR) {
            exitCode = ExitCode_Main_EventLoopFail;
        }
    }

    ClosePeripheralsAndHandlers();

    Log_Debug("Application exiting.\n");

    return exitCode;
}

/// <summary>
///     Button timer event:  Check the status of the button
/// </summary>
static void ButtonPollTimerEventHandler(EventLoopTimer *timer)
{
    if (ConsumeEventLoopTimerEvent(timer) != 0) {
        exitCode = ExitCode_ButtonTimer_Consume;
        return;
    }

    if (IsButtonPressed(sendMessageButtonGpioFd, &sendMessageButtonState)) {
        SendTelemetry("{\"ButtonPress\" : \"True\"}");
    }
}

/// <summary>
///     Azure timer event:  Check connection status and send telemetry
/// </summary>
static void AzureTimerEventHandler(EventLoopTimer *timer)
{
    if (ConsumeEventLoopTimerEvent(timer) != 0) {
        exitCode = ExitCode_AzureTimer_Consume;
        return;
    }

    // Check whether the device is connected to the internet.
    Networking_InterfaceConnectionStatus status;
    if (Networking_GetInterfaceConnectionStatus(NetworkInterface, &status) == 0) {
        if ((status & Networking_InterfaceConnectionStatus_ConnectedToInternet) &&
            (iotHubClientAuthenticationState == IoTHubClientAuthenticationState_NotAuthenticated)) {
            SetUpAzureIoTHubClient();
        }
    } else {
        if (errno != EAGAIN) {
            Log_Debug("ERROR: Networking_GetInterfaceConnectionStatus: %d (%s)\n", errno,
                      strerror(errno));
            exitCode = ExitCode_InterfaceConnectionStatus_Failed;
            return;
        }
    }

    if (iotHubClientAuthenticationState == IoTHubClientAuthenticationState_Authenticated) {
        telemetryCount++;
        if (telemetryCount == AzureIoTPollPeriodsPerTelemetry) {
            telemetryCount = 0;
            //SendSimulatedTelemetry();
            SendTempTelemetry();   
            //SendGPIO1Telemetry(); 
            //SendGPIO2Telemetry(); 
            //SendGPIO3Telemetry(); 
            //ReadWhoAmI();

        }
    }

    if (iothubClientHandle != NULL) {
        IoTHubDeviceClient_LL_DoWork(iothubClientHandle);
    }
}

/// <summary>
///     Parse the command line arguments given in the application manifest.
/// </summary>
static void ParseCommandLineArguments(int argc, char *argv[])
{
    int option = 0;
    static const struct option cmdLineOptions[] = {{"ConnectionType", required_argument, NULL, 'c'},
                                                   {"ScopeID", required_argument, NULL, 's'},
                                                   {"Hostname", required_argument, NULL, 'h'},
                                                   {"DeviceID", required_argument, NULL, 'd'},
                                                   {NULL, 0, NULL, 0}};

    // Loop over all of the options.
    while ((option = getopt_long(argc, argv, "c:s:h:d:", cmdLineOptions, NULL)) != -1) {
        // Check if arguments are missing. Every option requires an argument.
        if (optarg != NULL && optarg[0] == '-') {
            Log_Debug("WARNING: Option %c requires an argument\n", option);
            continue;
        }
        switch (option) {
        case 'c':
            Log_Debug("ConnectionType: %s\n", optarg);
            if (strcmp(optarg, "DPS") == 0) {
                connectionType = ConnectionType_DPS;
            } else if (strcmp(optarg, "Direct") == 0) {
                connectionType = ConnectionType_Direct;
            }
            break;
        case 's':
            Log_Debug("ScopeID: %s\n", optarg);
            scopeId = optarg;
            break;
        case 'h':
            Log_Debug("Hostname: %s\n", optarg);
            hubHostName = optarg;
            break;
        case 'd':
            Log_Debug("DeviceID: %s\n", optarg);
            deviceId = optarg;
            break;
        default:
            // Unknown options are ignored.
            break;
        }
    }
}

/// <summary>
///    Checks the number of transferred bytes for I2C functions and prints an error
///    message if the functions failed or if the number of bytes is different than
///    expected number of bytes to be transferred.
/// </summary>
/// <returns>true on success, or false on failure</returns>
static bool CheckTransferSize(const char *desc, size_t expectedBytes, ssize_t actualBytes)
{
    if (actualBytes < 0) {
        Log_Debug("ERROR: %s: errno=%d (%s)\n", desc, errno, strerror(errno));
        return false;
    }

    if (actualBytes != (ssize_t)expectedBytes) {
        Log_Debug("ERROR: %s: transferred %zd bytes; expected %zd\n", desc, actualBytes,
                  expectedBytes);
        return false;
    }

    return true;
}



/// <summary>
///     Validates if the values of the Scope ID, IotHub Hostname and Device ID were set.
/// </summary>
/// <returns>ExitCode_Success if the parameters were provided; otherwise another
/// ExitCode value which indicates the specific failure.</returns>
static ExitCode ValidateUserConfiguration(void)
{
    ExitCode validationExitCode = ExitCode_Success;

    if (connectionType < ConnectionType_DPS || connectionType > ConnectionType_Direct) {
        validationExitCode = ExitCode_Validate_ConnectionType;
    }

    if (connectionType == ConnectionType_DPS) {
        if (scopeId == NULL) {
            validationExitCode = ExitCode_Validate_ScopeId;
        } else {
            Log_Debug("Using DPS Connection: Azure IoT DPS Scope ID %s\n", scopeId);
        }
    }

    if (connectionType == ConnectionType_Direct) {
        if (hubHostName == NULL) {
            validationExitCode = ExitCode_Validate_IotHubHostname;
        } else if (deviceId == NULL) {
            validationExitCode = ExitCode_Validate_DeviceId;
        }
        if (deviceId != NULL) {
            // Validate that device ID is in lowercase.
            size_t len = strlen(deviceId);
            for (size_t i = 0; i < len; i++) {
                if (isupper(deviceId[i])) {
                    Log_Debug("Device ID must be in lowercase.\n");
                    return ExitCode_Validate_DeviceId;
                }
            }
        }
        if (validationExitCode == ExitCode_Success) {
            Log_Debug("Using Direct Connection: Azure IoT Hub Hostname %s\n", hubHostName);
        }
    }

    if (validationExitCode != ExitCode_Success) {
        Log_Debug("Command line arguments for application shoud be set as below\n%s",
                  cmdLineArgsUsageText);
    }
    return validationExitCode;
}

/// <summary>
///     Set up SIGTERM termination handler, initialize peripherals, and set up event handlers.
/// </summary>
/// <returns>
///     ExitCode_Success if all resources were allocated successfully; otherwise another
///     ExitCode value which indicates the specific failure.
/// </returns>
static ExitCode InitPeripheralsAndHandlers(void)
{
    struct sigaction action;
    memset(&action, 0, sizeof(struct sigaction));
    action.sa_handler = TerminationHandler;
    sigaction(SIGTERM, &action, NULL);

    eventLoop = EventLoop_Create();
    if (eventLoop == NULL) {
        Log_Debug("Could not create event loop.\n");
        return ExitCode_Init_EventLoop;
    }

    // Open SAMPLE_BUTTON_1 GPIO as input
    Log_Debug("Opening SAMPLE_BUTTON_1 as input.\n");
    sendMessageButtonGpioFd = GPIO_OpenAsInput(SAMPLE_BUTTON_1);
    if (sendMessageButtonGpioFd == -1) {
        Log_Debug("ERROR: Could not open SAMPLE_BUTTON_1: %s (%d).\n", strerror(errno), errno);
        return ExitCode_Init_MessageButton;
    }

    // Open GPIO0 GPIO as input
    Log_Debug("Opening GPIO11 as input.\n");
    sendMessageGpio0Fd = GPIO_OpenAsInput(MT3620_GPIO11);
    if (sendMessageGpio0Fd == -1) {
        Log_Debug("ERROR: Could not open SAMPLE_BUTTON_1: %s (%d).\n", strerror(errno), errno);
        return ExitCode_Init_MessageButton;
    }

    // Open GPIO1 GPIO as input
    Log_Debug("Opening GPIO1 as input.\n");
    sendMessageGpio1Fd = GPIO_OpenAsInput(MT3620_GPIO0);
    if (sendMessageGpio0Fd == -1) {
        Log_Debug("ERROR: Could not open SAMPLE_BUTTON_1: %s (%d).\n", strerror(errno), errno);
        return ExitCode_Init_MessageButton;
    }

    // Open GPIO2 GPIO as input
    Log_Debug("Opening GPIO2 as input.\n");
    sendMessageGpio2Fd = GPIO_OpenAsInput(MT3620_GPIO1);
    if (sendMessageGpio0Fd == -1) {
        Log_Debug("ERROR: Could not open SAMPLE_BUTTON_1: %s (%d).\n", strerror(errno), errno);
        return ExitCode_Init_MessageButton;
    }

    // Open GPIO3 GPIO as input
    Log_Debug("Opening GPIO3 as input.\n");
    sendMessageGpio3Fd = GPIO_OpenAsInput(MT3620_GPIO2);
    if (sendMessageGpio0Fd == -1) {
        Log_Debug("ERROR: Could not open SAMPLE_BUTTON_1: %s (%d).\n", strerror(errno), errno);
        return ExitCode_Init_MessageButton;
    }

     // Open I2Cs
    Log_Debug("Opening I2C as input.\n");
    GroveShield_Initialize(&i2cFd, 115200);
    sht31 = GroveTempHumiSHT31_Open(i2cFd);

    //int result = I2CMaster_SetBusSpeed(i2cFd, I2C_BUS_SPEED_STANDARD);
    //if (result != 0) {
    //    Log_Debug("ERROR: I2CMaster_SetBusSpeed: errno=%d (%s)\n", errno, strerror(errno));
    //    return ExitCode_Init_SetBusSpeed;
    //}

    //result = I2CMaster_SetTimeout(i2cFd, 1000);
    //if (result != 0) {
    //    Log_Debug("ERROR: I2CMaster_SetTimeout: errno=%d (%s)\n", errno, strerror(errno));
    //    return ExitCode_Init_SetTimeout;
    //}

    // SAMPLE_LED is used to show Device Twin settings state
    Log_Debug("Opening SAMPLE_LED as output.\n");
    deviceTwinStatusLedGpioFd =
        GPIO_OpenAsOutput(SAMPLE_LED, GPIO_OutputMode_PushPull, GPIO_Value_High);
    if (deviceTwinStatusLedGpioFd == -1) {
        Log_Debug("ERROR: Could not open SAMPLE_LED: %s (%d).\n", strerror(errno), errno);
        return ExitCode_Init_TwinStatusLed;
    }

    // RGB_LED is used to show Device Twin settings state
    Log_Debug("Opening RGB_LED as output.\n");
    deviceTwinRLedGpioFd =
        GPIO_OpenAsOutput(MT3620_RDB_LED2_RED, GPIO_OutputMode_PushPull, GPIO_Value_Low);
    deviceTwinGLedGpioFd =
        GPIO_OpenAsOutput(MT3620_RDB_LED2_GREEN, GPIO_OutputMode_PushPull, GPIO_Value_Low);
    deviceTwinBLedGpioFd =
        GPIO_OpenAsOutput(MT3620_RDB_LED2_BLUE, GPIO_OutputMode_PushPull, GPIO_Value_Low);
    //if (deviceTwinRLedGpioFd == -1) {
    //    Log_Debug("ERROR: Could not open R_LED: %s (%d).\n", strerror(errno), errno);
    //    return ExitCode_Init_TwinRLed;
    //}
    //if (deviceTwinGLedGpioFd == -1) {
    //    Log_Debug("ERROR: Could not open G_LED: %s (%d).\n", strerror(errno), errno);
    //    return ExitCode_Init_TwinGLed;
    //}
    //if (deviceTwinBLedGpioFd == -1) {
    //    Log_Debug("ERROR: Could not open B_LED: %s (%d).\n", strerror(errno), errno);
    //    return ExitCode_Init_TwinBLed;
    //}

    // Set up a timer to poll for button events.
    static const struct timespec buttonPressCheckPeriod = {.tv_sec = 0, .tv_nsec = 1000 * 1000};
    buttonPollTimer = CreateEventLoopPeriodicTimer(eventLoop, &ButtonPollTimerEventHandler,
                                                   &buttonPressCheckPeriod);
    if (buttonPollTimer == NULL) {
        return ExitCode_Init_ButtonPollTimer;
    }

    azureIoTPollPeriodSeconds = AzureIoTDefaultPollPeriodSeconds;
    struct timespec azureTelemetryPeriod = {.tv_sec = azureIoTPollPeriodSeconds, .tv_nsec = 0};
    azureTimer =
        CreateEventLoopPeriodicTimer(eventLoop, &AzureTimerEventHandler, &azureTelemetryPeriod);
    if (azureTimer == NULL) {
        return ExitCode_Init_AzureTimer;
    }

    return ExitCode_Success;
}

/// <summary>
///     Closes a file descriptor and prints an error on failure.
/// </summary>
/// <param name="fd">File descriptor to close</param>
/// <param name="fdName">File descriptor name to use in error message</param>
static void CloseFdAndPrintError(int fd, const char *fdName)
{
    if (fd >= 0) {
        int result = close(fd);
        if (result != 0) {
            Log_Debug("ERROR: Could not close fd %s: %s (%d).\n", fdName, strerror(errno), errno);
        }
    }
}

/// <summary>
///     Close peripherals and handlers.
/// </summary>
static void ClosePeripheralsAndHandlers(void)
{
    DisposeEventLoopTimer(buttonPollTimer);
    DisposeEventLoopTimer(azureTimer);
    EventLoop_Close(eventLoop);

    Log_Debug("Closing file descriptors\n");

    // Leave the LEDs off
    if (deviceTwinStatusLedGpioFd >= 0) {
        GPIO_SetValue(deviceTwinStatusLedGpioFd, GPIO_Value_High);
    }

    CloseFdAndPrintError(sendMessageButtonGpioFd, "SendMessageButton");
    CloseFdAndPrintError(deviceTwinStatusLedGpioFd, "StatusLed");
}

/// <summary>
///     Callback when the Azure IoT connection state changes.
///     This can indicate that a new connection attempt has succeeded or failed.
///     It can also indicate than an existing connection has expired due to SAS token expiry.
/// </summary>
static void ConnectionStatusCallback(IOTHUB_CLIENT_CONNECTION_STATUS result,
                                     IOTHUB_CLIENT_CONNECTION_STATUS_REASON reason,
                                     void *userContextCallback)
{
    Log_Debug("Azure IoT connection status: %s\n", GetReasonString(reason));

    if (result != IOTHUB_CLIENT_CONNECTION_AUTHENTICATED) {
        iotHubClientAuthenticationState = IoTHubClientAuthenticationState_NotAuthenticated;
        return;
    }

    iotHubClientAuthenticationState = IoTHubClientAuthenticationState_Authenticated;

    // Send static device twin properties when connection is established.
    TwinReportState("{\"manufacturer\":\"Microsoft\",\"model\":\"Azure Sphere Sample Device\"}");
}

/// <summary>
///     Sets up the Azure IoT Hub connection (creates the iothubClientHandle)
///     When the SAS Token for a device expires the connection needs to be recreated
///     which is why this is not simply a one time call.
/// </summary>
static void SetUpAzureIoTHubClient(void)
{
    bool isClientSetupSuccessful = false;

    if (iothubClientHandle != NULL) {
        IoTHubDeviceClient_LL_Destroy(iothubClientHandle);
    }

    if (connectionType == ConnectionType_Direct) {
        isClientSetupSuccessful = SetUpAzureIoTHubClientWithDaa();
    } else if (connectionType == ConnectionType_DPS) {
        isClientSetupSuccessful = SetUpAzureIoTHubClientWithDps();
    }

    if (!isClientSetupSuccessful) {
        // If we fail to connect, reduce the polling frequency, starting at
        // AzureIoTMinReconnectPeriodSeconds and with a backoff up to
        // AzureIoTMaxReconnectPeriodSeconds
        if (azureIoTPollPeriodSeconds == AzureIoTDefaultPollPeriodSeconds) {
            azureIoTPollPeriodSeconds = AzureIoTMinReconnectPeriodSeconds;
        } else {
            azureIoTPollPeriodSeconds *= 2;
            if (azureIoTPollPeriodSeconds > AzureIoTMaxReconnectPeriodSeconds) {
                azureIoTPollPeriodSeconds = AzureIoTMaxReconnectPeriodSeconds;
            }
        }

        struct timespec azureTelemetryPeriod = {azureIoTPollPeriodSeconds, 0};
        SetEventLoopTimerPeriod(azureTimer, &azureTelemetryPeriod);

        Log_Debug("ERROR: Failed to create IoTHub Handle - will retry in %i seconds.\n",
                  azureIoTPollPeriodSeconds);
        return;
    }

    // Successfully connected, so make sure the polling frequency is back to the default
    azureIoTPollPeriodSeconds = AzureIoTDefaultPollPeriodSeconds;
    struct timespec azureTelemetryPeriod = {.tv_sec = azureIoTPollPeriodSeconds, .tv_nsec = 0};
    SetEventLoopTimerPeriod(azureTimer, &azureTelemetryPeriod);

    // Set client authentication state to initiated. This is done to indicate that
    // SetUpAzureIoTHubClient() has been called (and so should not be called again) while the
    // client is waiting for a response via the ConnectionStatusCallback().
    iotHubClientAuthenticationState = IoTHubClientAuthenticationState_AuthenticationInitiated;

    IoTHubDeviceClient_LL_SetDeviceTwinCallback(iothubClientHandle, DeviceTwinCallback, NULL);
    IoTHubDeviceClient_LL_SetDeviceMethodCallback(iothubClientHandle, DeviceMethodCallback, NULL);
    IoTHubDeviceClient_LL_SetConnectionStatusCallback(iothubClientHandle, ConnectionStatusCallback,
                                                      NULL);
}

/// <summary>
///     Sets up the Azure IoT Hub connection (creates the iothubClientHandle)
///     with DAA
/// </summary>
static bool SetUpAzureIoTHubClientWithDaa(void)
{
    // Set up auth type
    int retError = iothub_security_init(IOTHUB_SECURITY_TYPE_X509);
    if (retError != 0) {
        Log_Debug("ERROR: iothub_security_init failed with error %d.\n", retError);
        return false;
    }

    // Create Azure Iot Hub client handle
    iothubClientHandle =
        IoTHubDeviceClient_LL_CreateFromDeviceAuth(hubHostName, deviceId, MQTT_Protocol);

    if (iothubClientHandle == NULL) {
        Log_Debug("IoTHubDeviceClient_LL_CreateFromDeviceAuth returned NULL.\n");
        return false;
    }

    // Enable DAA cert usage when x509 is invoked
    if (IoTHubDeviceClient_LL_SetOption(iothubClientHandle, "SetDeviceId",
                                        &deviceIdForDaaCertUsage) != IOTHUB_CLIENT_OK) {
        Log_Debug("ERROR: Failure setting Azure IoT Hub client option \"SetDeviceId\".\n");
        return false;
    }

    return true;
}

/// <summary>
///     Sets up the Azure IoT Hub connection (creates the iothubClientHandle)
///     with DPS
/// </summary>
static bool SetUpAzureIoTHubClientWithDps(void)
{
    AZURE_SPHERE_PROV_RETURN_VALUE provResult =
        IoTHubDeviceClient_LL_CreateWithAzureSphereDeviceAuthProvisioning(scopeId, 10000,
                                                                          &iothubClientHandle);
    Log_Debug("IoTHubDeviceClient_LL_CreateWithAzureSphereDeviceAuthProvisioning returned '%s'.\n",
              GetAzureSphereProvisioningResultString(provResult));

    if (provResult.result != AZURE_SPHERE_PROV_RESULT_OK) {
        return false;
    }

    return true;
}

/// <summary>
///     Callback invoked when a Direct Method is received from Azure IoT Hub.
/// </summary>
static int DeviceMethodCallback(const char *methodName, const unsigned char *payload,
                                size_t payloadSize, unsigned char **response, size_t *responseSize,
                                void *userContextCallback)
{
    int result;
    char *responseString;

    Log_Debug("Received Device Method callback: Method name %s.\n", methodName);

    if (strcmp("TriggerAlarm", methodName) == 0) {
        // Output alarm using Log_Debug
        Log_Debug("  ----- ALARM TRIGGERED! -----\n");
        responseString = "\"Alarm Triggered\""; // must be a JSON string (in quotes)
        result = 200;
    } else {
        // All other method names are ignored
        responseString = "{}";
        result = -1;
    }

    // if 'response' is non-NULL, the Azure IoT library frees it after use, so copy it to heap
    *responseSize = strlen(responseString);
    *response = malloc(*responseSize);
    memcpy(*response, responseString, *responseSize);
    return result;
}

/// <summary>
///     Callback invoked when a Device Twin update is received from Azure IoT Hub.
/// </summary>
static void DeviceTwinCallback(DEVICE_TWIN_UPDATE_STATE updateState, const unsigned char *payload,
                               size_t payloadSize, void *userContextCallback)
{
    size_t nullTerminatedJsonSize = payloadSize + 1;
    char *nullTerminatedJsonString = (char *)malloc(nullTerminatedJsonSize);
    if (nullTerminatedJsonString == NULL) {
        Log_Debug("ERROR: Could not allocate buffer for twin update payload.\n");
        abort();
    }

    // Copy the provided buffer to a null terminated buffer.
    memcpy(nullTerminatedJsonString, payload, payloadSize);
    // Add the null terminator at the end.
    nullTerminatedJsonString[nullTerminatedJsonSize - 1] = 0;

    JSON_Value *rootProperties = NULL;
    rootProperties = json_parse_string(nullTerminatedJsonString);
    if (rootProperties == NULL) {
        Log_Debug("WARNING: Cannot parse the string as JSON content.\n");
        goto cleanup;
    }

    JSON_Object *rootObject = json_value_get_object(rootProperties);
    JSON_Object *desiredProperties = json_object_dotget_object(rootObject, "desired");
    if (desiredProperties == NULL) {
        desiredProperties = rootObject;
    }

    // The desired properties should have a "StatusLED" object
    int statusLedValue = json_object_dotget_boolean(desiredProperties, "StatusLED");
    if (statusLedValue != -1) {
        statusLedOn = statusLedValue == 1;
        GPIO_SetValue(deviceTwinStatusLedGpioFd, statusLedOn ? GPIO_Value_Low : GPIO_Value_High);
    }

    // Report current status LED state
    if (statusLedOn) {
        TwinReportState("{\"StatusLED\":true}");
    } else {
        TwinReportState("{\"StatusLED\":false}");
    }

    // The desired properties should have a "RGBLED" object
    int RLedValue = json_object_dotget_boolean(desiredProperties, "RLED");
    int GLedValue = json_object_dotget_boolean(desiredProperties, "GLED");
    int BLedValue = json_object_dotget_boolean(desiredProperties, "BLED");
    if (RLedValue != -1) {
        RLedOn = RLedValue == 1;
        GPIO_SetValue(deviceTwinRLedGpioFd, RLedOn ? GPIO_Value_Low : GPIO_Value_High);
    }
    if (GLedValue != -1) {
        GLedOn = GLedValue == 1;
        GPIO_SetValue(deviceTwinGLedGpioFd, GLedOn ? GPIO_Value_Low : GPIO_Value_High);
    }
    if (BLedValue != -1) {
        BLedOn = BLedValue == 1;
        GPIO_SetValue(deviceTwinBLedGpioFd, BLedOn ? GPIO_Value_Low : GPIO_Value_High);
    }
    // Report current status LED state
    if (RLedOn) {
        TwinReportState("{\"RLED\":true}");
    } else {
        TwinReportState("{\"RLED\":false}");
    }
    // Report current status LED state
    if (GLedOn) {
        TwinReportState("{\"GLED\":true}");
    } else {
        TwinReportState("{\"GLED\":false}");
    }
    // Report current status LED state
    if (BLedOn) {
        TwinReportState("{\"BLED\":true}");
    } else {
        TwinReportState("{\"BLED\":false}");
    }

cleanup:
    // Release the allocated memory.
    json_value_free(rootProperties);
    free(nullTerminatedJsonString);
}

/// <summary>
///     Converts the Azure IoT Hub connection status reason to a string.
/// </summary>
static const char *GetReasonString(IOTHUB_CLIENT_CONNECTION_STATUS_REASON reason)
{
    static char *reasonString = "unknown reason";
    switch (reason) {
    case IOTHUB_CLIENT_CONNECTION_EXPIRED_SAS_TOKEN:
        reasonString = "IOTHUB_CLIENT_CONNECTION_EXPIRED_SAS_TOKEN";
        break;
    case IOTHUB_CLIENT_CONNECTION_DEVICE_DISABLED:
        reasonString = "IOTHUB_CLIENT_CONNECTION_DEVICE_DISABLED";
        break;
    case IOTHUB_CLIENT_CONNECTION_BAD_CREDENTIAL:
        reasonString = "IOTHUB_CLIENT_CONNECTION_BAD_CREDENTIAL";
        break;
    case IOTHUB_CLIENT_CONNECTION_RETRY_EXPIRED:
        reasonString = "IOTHUB_CLIENT_CONNECTION_RETRY_EXPIRED";
        break;
    case IOTHUB_CLIENT_CONNECTION_NO_NETWORK:
        reasonString = "IOTHUB_CLIENT_CONNECTION_NO_NETWORK";
        break;
    case IOTHUB_CLIENT_CONNECTION_COMMUNICATION_ERROR:
        reasonString = "IOTHUB_CLIENT_CONNECTION_COMMUNICATION_ERROR";
        break;
    case IOTHUB_CLIENT_CONNECTION_OK:
        reasonString = "IOTHUB_CLIENT_CONNECTION_OK";
        break;
    case IOTHUB_CLIENT_CONNECTION_NO_PING_RESPONSE:
        reasonString = "IOTHUB_CLIENT_CONNECTION_NO_PING_RESPONSE";
        break;
    }
    return reasonString;
}

/// <summary>
///     Converts AZURE_SPHERE_PROV_RETURN_VALUE to a string.
/// </summary>
static const char *GetAzureSphereProvisioningResultString(
    AZURE_SPHERE_PROV_RETURN_VALUE provisioningResult)
{
    switch (provisioningResult.result) {
    case AZURE_SPHERE_PROV_RESULT_OK:
        return "AZURE_SPHERE_PROV_RESULT_OK";
    case AZURE_SPHERE_PROV_RESULT_INVALID_PARAM:
        return "AZURE_SPHERE_PROV_RESULT_INVALID_PARAM";
    case AZURE_SPHERE_PROV_RESULT_NETWORK_NOT_READY:
        return "AZURE_SPHERE_PROV_RESULT_NETWORK_NOT_READY";
    case AZURE_SPHERE_PROV_RESULT_DEVICEAUTH_NOT_READY:
        return "AZURE_SPHERE_PROV_RESULT_DEVICEAUTH_NOT_READY";
    case AZURE_SPHERE_PROV_RESULT_PROV_DEVICE_ERROR:
        return "AZURE_SPHERE_PROV_RESULT_PROV_DEVICE_ERROR";
    case AZURE_SPHERE_PROV_RESULT_GENERIC_ERROR:
        return "AZURE_SPHERE_PROV_RESULT_GENERIC_ERROR";
    default:
        return "UNKNOWN_RETURN_VALUE";
    }
}

/// <summary>
///     Check the network status.
/// </summary>
static bool IsConnectionReadyToSendTelemetry(void)
{
    Networking_InterfaceConnectionStatus status;
    if (Networking_GetInterfaceConnectionStatus(NetworkInterface, &status) != 0) {
        if (errno != EAGAIN) {
            Log_Debug("ERROR: Networking_GetInterfaceConnectionStatus: %d (%s)\n", errno,
                      strerror(errno));
            exitCode = ExitCode_InterfaceConnectionStatus_Failed;
            return false;
        }
        Log_Debug(
            "WARNING: Cannot send Azure IoT Hub telemetry because the networking stack isn't ready "
            "yet.\n");
        return false;
    }

    if ((status & Networking_InterfaceConnectionStatus_ConnectedToInternet) == 0) {
        Log_Debug(
            "WARNING: Cannot send Azure IoT Hub telemetry because the device is not connected to "
            "the internet.\n");
        return false;
    }

    return true;
}

/// <summary>
///     Sends telemetry to Azure IoT Hub
/// </summary>
static void SendTelemetry(const char *jsonMessage)
{
    if (iotHubClientAuthenticationState != IoTHubClientAuthenticationState_Authenticated) {
        // AzureIoT client is not authenticated. Log a warning and return.
        Log_Debug("WARNING: Azure IoT Hub is not authenticated. Not sending telemetry.\n");
        return;
    }

    Log_Debug("Sending Azure IoT Hub telemetry: %s.\n", jsonMessage);

    // Check whether the device is connected to the internet.
    if (IsConnectionReadyToSendTelemetry() == false) {
        return;
    }

    IOTHUB_MESSAGE_HANDLE messageHandle = IoTHubMessage_CreateFromString(jsonMessage);

    if (messageHandle == 0) {
        Log_Debug("ERROR: unable to create a new IoTHubMessage.\n");
        return;
    }

    if (IoTHubDeviceClient_LL_SendEventAsync(iothubClientHandle, messageHandle, SendEventCallback,
                                             /*&callback_param*/ NULL) != IOTHUB_CLIENT_OK) {
        Log_Debug("ERROR: failure requesting IoTHubClient to send telemetry event.\n");
    } else {
        Log_Debug("INFO: IoTHubClient accepted the telemetry event for delivery.\n");
    }

    IoTHubMessage_Destroy(messageHandle);
}

/// <summary>
///     Callback invoked when the Azure IoT Hub send event request is processed.
/// </summary>
static void SendEventCallback(IOTHUB_CLIENT_CONFIRMATION_RESULT result, void *context)
{
    Log_Debug("INFO: Azure IoT Hub send telemetry event callback: status code %d.\n", result);
}

/// <summary>
///     Enqueues a report containing Device Twin reported properties. The report is not sent
///     immediately, but it is sent on the next invocation of IoTHubDeviceClient_LL_DoWork().
/// </summary>
static void TwinReportState(const char *jsonState)
{
    if (iothubClientHandle == NULL) {
        Log_Debug("ERROR: Azure IoT Hub client not initialized.\n");
    } else {
        if (IoTHubDeviceClient_LL_SendReportedState(
                iothubClientHandle, (const unsigned char *)jsonState, strlen(jsonState),
                ReportedStateCallback, NULL) != IOTHUB_CLIENT_OK) {
            Log_Debug("ERROR: Azure IoT Hub client error when reporting state '%s'.\n", jsonState);
        } else {
            Log_Debug("INFO: Azure IoT Hub client accepted request to report state '%s'.\n",
                      jsonState);
        }
    }
}

/// <summary>
///     Callback invoked when the Device Twin report state request is processed by Azure IoT Hub
///     client.
/// </summary>
static void ReportedStateCallback(int result, void *context)
{
    Log_Debug("INFO: Azure IoT Hub Device Twin reported state callback: status code %d.\n", result);
}

#define TELEMETRY_BUFFER_SIZE 100

/// <summary>
///     Generate simulated telemetry and send to Azure IoT Hub.
/// </summary>
void SendSimulatedTelemetry(void)
{
    // Generate a simulated temperature.
    static float temperature = 50.0f;                    // starting temperature
    float delta = ((float)(rand() % 41)) / 20.0f - 1.0f; // between -1.0 and +1.0
    temperature += delta;

    char telemetryBuffer[TELEMETRY_BUFFER_SIZE];
    int len =
        snprintf(telemetryBuffer, TELEMETRY_BUFFER_SIZE, "{\"Temperature\":%3.2f}", temperature);
    if (len < 0 || len >= TELEMETRY_BUFFER_SIZE) {
        Log_Debug("ERROR: Cannot write telemetry to buffer.\n");
        return;
    }
    SendTelemetry(telemetryBuffer);
}

/// <summary>
///     Check whether a given button has just been pressed.
/// </summary>
/// <param name="fd">The button file descriptor</param>
/// <param name="oldState">Old state of the button (pressed or released)</param>
/// <returns>true if pressed, false otherwise</returns>
static bool IsButtonPressed(int fd, GPIO_Value_Type *oldState)
{
    bool isButtonPressed = false;
    GPIO_Value_Type newState;
    int result = GPIO_GetValue(fd, &newState);
    if (result != 0) {
        Log_Debug("ERROR: Could not read button GPIO: %s (%d).\n", strerror(errno), errno);
        exitCode = ExitCode_IsButtonPressed_GetValue;
    } else {
        // Button is pressed if it is low and different than last known state.
        isButtonPressed = (newState != *oldState) && (newState == GPIO_Value_Low);
        *oldState = newState;
    }

    return isButtonPressed;
}





void SendTempTelemetry(void)
{
    const struct timespec sleepTime = {1, 0};
    char telemetryBufferTemp[TELEMETRY_BUFFER_SIZE];
    char telemetryBufferHum[TELEMETRY_BUFFER_SIZE];
    //void* sht31 = GroveTempHumiSHT31_Open(i2cFd);
    GroveTempHumiSHT31_Read(sht31);
    float temp = GroveTempHumiSHT31_GetTemperature(sht31);
    float humi = GroveTempHumiSHT31_GetHumidity(sht31);
    Log_Debug("Temperature: %.1fC\n", temp);
    Log_Debug("Humidity: %.1f\%c\n", humi, 0x25);

    //GPIO_SetValue(deviceTwinStatusLedGpioFd, GPIO_Value_Low);
    //nanosleep(&sleepTime, NULL);

    //GPIO_SetValue(deviceTwinStatusLedGpioFd, GPIO_Value_High);
    //nanosleep(&sleepTime, NULL);

    int len0 = snprintf(telemetryBufferTemp, TELEMETRY_BUFFER_SIZE, "{\"Temperature\":%3.2f}", temp);
    if (len0 < 0 || len0 >= TELEMETRY_BUFFER_SIZE) {
        Log_Debug("ERROR: Cannot write temp telemetry to buffer.\n");
        return;
    }

    int len1 =
        snprintf(telemetryBufferHum, TELEMETRY_BUFFER_SIZE, "{\"Humidity\":%3.2f}", humi);
    if (len1 < 0 || len1 >= TELEMETRY_BUFFER_SIZE) {
        Log_Debug("ERROR: Cannot write hum telemetry to buffer.\n");
        return;
    }

    SendTelemetry(telemetryBufferTemp);
    SendTelemetry(telemetryBufferHum);
}

//
//void SendTempTelemetry(void)
//{
//    char telemetryBufferTemp[TELEMETRY_BUFFER_SIZE];
//    char telemetryBufferHum[TELEMETRY_BUFFER_SIZE];
//    uint8_t readData[6];
//
//
//    uint8_t writeDataS[2];
//    writeDataS[0] = (uint8_t)(CMD_SOFT_RESET >> 8);
//    writeDataS[1] = (uint8_t)(CMD_SOFT_RESET & 0xff);
//    I2CMaster_Write(i2cFd, SHT31_ADDRESS, writeDataS, sizeof(writeDataS));
//    sleep(20);
//
//    uint8_t writeData[2];
//    writeData[0] = (uint8_t)(CMD_SINGLE_HIGH >> 8);
//    writeData[1] = (uint8_t)(CMD_SINGLE_HIGH & 0xff);
//
//    I2CMaster_Write(i2cFd, SHT31_ADDRESS, writeData, sizeof(writeData));
//
//    sleep(20);
//
//    I2CMaster_Read(i2cFd, SHT31_ADDRESS, readData, sizeof(readData));
//
//    	if (readData[2] != CalcCRC8(&readData[0], 2))
//           Log_Debug("ERROR: temperature CRC failed.\n");
//        if (readData[5] != CalcCRC8(&readData[3], 2))
//            Log_Debug("ERROR: humidity CRC failed.\n");
//
//        uint16_t ST;
//        ST = readData[0];
//        ST = (uint16_t)(ST << 8);
//        ST = (uint16_t)(ST | readData[1]);
//
//        uint16_t SRH;
//        SRH = readData[3];
//        SRH = (uint16_t)(SRH << 8);
//        SRH = (uint16_t)(SRH | readData[4]);
//
//        float Temperature = NAN;
//        float Humidity = NAN;
//        Temperature = (float)ST * 175 / 0xffff - 45;
//        Humidity = (float)SRH * 100 / 0xffff;
//
//        int len0 = snprintf(telemetryBufferTemp, TELEMETRY_BUFFER_SIZE, "{\"Real Temperature\":%3.2f}", Temperature);
//        if (len0 < 0 || len0 >= TELEMETRY_BUFFER_SIZE) {
//            Log_Debug("ERROR: Cannot write temp telemetry to buffer.\n");
//            return;
//        }
//
//        int len1 = snprintf(telemetryBufferHum, TELEMETRY_BUFFER_SIZE, "{\"Real Humidity\":%3.2f}", Humidity); 
//        if (len1 < 0 || len1 >= TELEMETRY_BUFFER_SIZE) {
//            Log_Debug("ERROR: Cannot write hum telemetry to buffer.\n");
//            return;
//        }
//
//        SendTelemetry(telemetryBufferTemp);
//        SendTelemetry(telemetryBufferHum);
//}


void SendGPIO3Telemetry(void)
{
    //    GPIO_Value_Type newState3;
    //    int result3 = GPIO_GetValue(sendMessageGpio3Fd, &newState3);
    //    char telemetryBuffer3[TELEMETRY_BUFFER_SIZE];
    //    int len3 =
    //        snprintf(telemetryBuffer3, TELEMETRY_BUFFER_SIZE, "{\"GPIO3\":%d}", result3);
    //    if (len3 < 0 || len3 >= TELEMETRY_BUFFER_SIZE) {
    //        Log_Debug("ERROR: Cannot write telemetry to buffer.\n");
    //        return;
    //    }
    //    SendTelemetry(telemetryBuffer3);
}

void SendGPIO2Telemetry(void)
{
    // GPIO_Value_Type newState2;
    // int result2 = GPIO_GetValue(sendMessageGpio2Fd, &newState2);
    // char telemetryBuffer2[TELEMETRY_BUFFER_SIZE];
    // int len2 = snprintf(telemetryBuffer2, TELEMETRY_BUFFER_SIZE, "{\"GPIO2\":%d}", result2);
    // if (len2 < 0 || len2 >= TELEMETRY_BUFFER_SIZE) {
    //    Log_Debug("ERROR: Cannot write telemetry to buffer.\n");
    //    return;
    //}
    // SendTelemetry(telemetryBuffer2);
}

void SendGPIO1Telemetry(void)
{
    // GPIO_Value_Type newState1;
    // int result1 = GPIO_GetValue(sendMessageGpio1Fd, &newState1);
    // char telemetryBuffer1[TELEMETRY_BUFFER_SIZE];
    // int len1 = snprintf(telemetryBuffer1, TELEMETRY_BUFFER_SIZE, "{\"GPIO1\":%d}", result1);
    // if (len1 < 0 || len1 >= TELEMETRY_BUFFER_SIZE) {
    //    Log_Debug("ERROR: Cannot write telemetry to buffer.\n");
    //    return;
    //}
    // SendTelemetry(telemetryBuffer1);
}

// void SendTempTelemetry(void)
//{
// float tempv = 20.0f;
// char telemetryBufferTemp[TELEMETRY_BUFFER_SIZE];
// int len0 = snprintf(telemetryBufferTemp, TELEMETRY_BUFFER_SIZE, "{\"Real Temperature\":%3.2f}",
// tempv); if (len0 < 0 || len0 >= TELEMETRY_BUFFER_SIZE) {
//    Log_Debug("ERROR: Cannot write telemetry to buffer.\n");
//    return;
//}
// SendTelemetry(telemetryBufferTemp);
//}

//#define SHT31_ADDRESS (0x44 << 1)
////#define SHT31_ADDRESS (0x00)
//#define CMD_SINGLE_HIGH (0x2400)
//#define CMD_SOFT_RESET (0x30a2)
//#define POLYNOMIAL (0x31)

// static uint8_t CalcCRC8(const uint8_t *data, int dataSize)
//{
//    uint8_t crc = 0xff;
//
//    for (int j = dataSize; j > 0; j--) {
//        crc ^= *data++;
//
//        for (int i = 8; i > 0; i--) {
//            crc = (crc & 0x80) != 0 ? (uint8_t)(crc << 1 ^ POLYNOMIAL) : (uint8_t)(crc << 1);
//        }
//    }
//
//    return crc;
//}

//static const uint8_t lsm6ds3Address = 0x6A;
//static ExitCode ReadWhoAmI(void)
//{
//    // DocID026899 Rev 10, S9.11, WHO_AM_I (0Fh); has fixed value 0x69.
//    static const uint8_t whoAmIRegId = 0x0F;
//    static const uint8_t expectedWhoAmI = 0x69;
//    uint8_t actualWhoAmI;
//
//    // Read register value using AppLibs combination read and write API.
//    ssize_t transferredBytes =
//        I2CMaster_WriteThenRead(i2cFd, lsm6ds3Address, &whoAmIRegId, sizeof(whoAmIRegId),
//                                &actualWhoAmI, sizeof(actualWhoAmI));
//    if (!CheckTransferSize("I2CMaster_WriteThenRead (WHO_AM_I)",
//                           sizeof(whoAmIRegId) + sizeof(actualWhoAmI), transferredBytes)) {
//        return ExitCode_ReadWhoAmI_WriteThenRead;
//    }
//    Log_Debug("INFO: WHO_AM_I=0x%02x (I2CMaster_WriteThenRead)\n", actualWhoAmI);
//    if (actualWhoAmI != expectedWhoAmI) {
//        Log_Debug("ERROR: Unexpected WHO_AM_I value.\n");
//        return ExitCode_ReadWhoAmI_WriteThenReadCompare;
//    }
//
//    // Read register value using AppLibs separate read and write APIs.
//    transferredBytes = I2CMaster_Write(i2cFd, lsm6ds3Address, &whoAmIRegId, sizeof(whoAmIRegId));
//    if (!CheckTransferSize("I2CMaster_Write (WHO_AM_I)", sizeof(whoAmIRegId), transferredBytes)) {
//        return ExitCode_ReadWhoAmI_Write;
//    }
//    transferredBytes = I2CMaster_Read(i2cFd, lsm6ds3Address, &actualWhoAmI, sizeof(actualWhoAmI));
//    if (!CheckTransferSize("I2CMaster_Read (WHO_AM_I)", sizeof(actualWhoAmI), transferredBytes)) {
//        return ExitCode_ReadWhoAmI_Read;
//    }
//    Log_Debug("INFO: WHO_AM_I=0x%02x (I2CMaster_Write + I2CMaster_Read)\n", actualWhoAmI);
//    if (actualWhoAmI != expectedWhoAmI) {
//        Log_Debug("ERROR: Unexpected WHO_AM_I value.\n");
//        return ExitCode_ReadWhoAmI_WriteReadCompare;
//    }
//
//    // Read register value using POSIX APIs.
//    // This uses the I2C target address which was set earlier with
//    // I2CMaster_SetDefaultTargetAddress.
//    transferredBytes = write(i2cFd, &whoAmIRegId, sizeof(whoAmIRegId));
//    if (!CheckTransferSize("write (WHO_AM_I)", sizeof(whoAmIRegId), transferredBytes)) {
//        return ExitCode_ReadWhoAmI_PosixWrite;
//    }
//    transferredBytes = read(i2cFd, &actualWhoAmI, sizeof(actualWhoAmI));
//    if (!CheckTransferSize("read (WHO_AM_I)", sizeof(actualWhoAmI), transferredBytes)) {
//        return ExitCode_ReadWhoAmI_PosixRead;
//    }
//    Log_Debug("INFO: WHO_AM_I=0x%02x (POSIX read + write)\n", actualWhoAmI);
//    if (actualWhoAmI != expectedWhoAmI) {
//        Log_Debug("ERROR: Unexpected WHO_AM_I value.\n");
//        return ExitCode_ReadWhoAmI_PosixCompare;
//    }
//
//    return ExitCode_Success;
//}
