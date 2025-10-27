# Reference: rclcpp/rclcpp_components/cmake/rclcpp_components_register_node.cmake
# This macro is based on rclcpp_components_register_node, modified to use Agnocast executors.

# agnocast_components_register_node
#
# 単一のcomponentを静的にロードする実行ファイルを生成
#
# :param target: componentライブラリのターゲット名
# :param PLUGIN: component classの完全修飾名（例: "my_namespace::MyComponent"）
# :param EXECUTABLE: 生成する実行ファイル名
# :param EXECUTOR: Executorタイプ（"SingleThreaded" または "MultiThreaded"、デフォルト: "MultiThreaded"）
# :param NUMBER_OF_ROS2_THREADS: ROS2スレッド数（MultiThreadedの場合、デフォルト: 0 = 自動）
# :param NUMBER_OF_AGNOCAST_THREADS: Agnocastスレッド数（MultiThreadedの場合、デフォルト: 0 = 自動）
# :param GET_NEXT_TIMEOUT_MS: タイムアウト（SingleThreadedの場合、デフォルト: 50ms）
#
function(agnocast_components_register_node target)
  cmake_parse_arguments(ARGS
    ""
    "PLUGIN;EXECUTABLE;EXECUTOR;NUMBER_OF_ROS2_THREADS;NUMBER_OF_AGNOCAST_THREADS;GET_NEXT_TIMEOUT_MS"
    ""
    ${ARGN}
  )

  # 必須パラメータチェック
  if(NOT ARGS_PLUGIN)
    message(FATAL_ERROR "agnocast_components_register_node: PLUGIN argument required")
  endif()
  if(NOT ARGS_EXECUTABLE)
    message(FATAL_ERROR "agnocast_components_register_node: EXECUTABLE argument required")
  endif()

  # Executorタイプのデフォルト値
  if(NOT ARGS_EXECUTOR)
    set(ARGS_EXECUTOR "MultiThreaded")
  endif()

  # ライブラリパスの取得
  get_target_property(target_type ${target} TYPE)
  if(target_type STREQUAL "SHARED_LIBRARY")
    set(library_name "$<TARGET_FILE:${target}>")
  else()
    message(FATAL_ERROR "agnocast_components_register_node: target must be a SHARED_LIBRARY")
  endif()

  # Executor設定コードの生成
  # Reference: src/middleware/external/agnocast/src/agnocastlib/src/agnocast_component_container_mt.cpp (lines 30-32)
  if(ARGS_EXECUTOR STREQUAL "MultiThreaded")
    # デフォルト値設定
    if(NOT ARGS_NUMBER_OF_ROS2_THREADS)
      set(ARGS_NUMBER_OF_ROS2_THREADS "0")
    endif()
    if(NOT ARGS_NUMBER_OF_AGNOCAST_THREADS)
      set(ARGS_NUMBER_OF_AGNOCAST_THREADS "0")
    endif()

    set(executor_setup "    // MultiThreaded Agnocast Executor
    auto executor = std::make_shared<agnocast::MultiThreadedAgnocastExecutor>(
      rclcpp::ExecutorOptions{},
      ${ARGS_NUMBER_OF_ROS2_THREADS},  // number_of_ros2_threads
      ${ARGS_NUMBER_OF_AGNOCAST_THREADS},  // number_of_agnocast_threads
      false,  // yield_before_execute
      std::chrono::nanoseconds(10 * 1000 * 1000),  // ros2_next_exec_timeout_ns
      10  // agnocast_next_exec_timeout_ms
    );")
  # Reference: src/middleware/external/agnocast/src/agnocastlib/src/agnocast_component_container.cpp (lines 19-20)
  elseif(ARGS_EXECUTOR STREQUAL "SingleThreaded")
    # デフォルト値設定
    if(NOT ARGS_GET_NEXT_TIMEOUT_MS)
      set(ARGS_GET_NEXT_TIMEOUT_MS "50")
    endif()

    set(executor_setup "    // SingleThreaded Agnocast Executor
    auto executor = std::make_shared<agnocast::SingleThreadedAgnocastExecutor>(
      rclcpp::ExecutorOptions{},
      ${ARGS_GET_NEXT_TIMEOUT_MS}  // get_next_timeout_ms
    );")
  else()
    message(FATAL_ERROR "agnocast_components_register_node: EXECUTOR must be 'SingleThreaded' or 'MultiThreaded'")
  endif()

  set(class_name "${ARGS_PLUGIN}")

  # テンプレートからmain関数ソースを生成
  set(generated_source "${CMAKE_CURRENT_BINARY_DIR}/agnocast_node_main_${ARGS_EXECUTABLE}.cpp")
  configure_file(
    "${agnocastlib_DIR}/../cmake/agnocast_node_main.cpp.in"
    "${generated_source}"
    @ONLY
  )

  # 実行ファイルの作成
  add_executable(${ARGS_EXECUTABLE} "${generated_source}")

  # ターゲットのリンク
  target_link_libraries(${ARGS_EXECUTABLE}
    ${target}
    agnocast
    rclcpp::rclcpp
    ${class_loader_TARGETS}
  )

  # rclcpp_componentsへの依存
  ament_target_dependencies(${ARGS_EXECUTABLE}
    rclcpp
    rclcpp_components
    class_loader
  )

  # インストール
  install(TARGETS ${ARGS_EXECUTABLE}
    DESTINATION lib/${PROJECT_NAME}
  )

  message(STATUS "agnocast_components_register_node: Created executable '${ARGS_EXECUTABLE}' for component '${ARGS_PLUGIN}'")
endfunction()
