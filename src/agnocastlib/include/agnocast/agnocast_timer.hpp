#include <chrono>
#include <functional>
#include <stdexcept>

namespace agnocast
{

class AgnocastTimer
{
public:
  /**
   * @brief Construct a new Agnocast Timer object
   *
   * @param period Timer period in nanoseconds
   * @param callback Function to call when timer expires
   * @throws std::runtime_error if timer creation fails
   */
  AgnocastTimer(std::chrono::nanoseconds period, std::function<void()> callback);

  /**
   * @brief Destroy the Agnocast Timer object
   */
  ~AgnocastTimer();

  // Disable copy and move
  AgnocastTimer(const AgnocastTimer &) = delete;
  AgnocastTimer & operator=(const AgnocastTimer &) = delete;
  AgnocastTimer(AgnocastTimer &&) = delete;
  AgnocastTimer & operator=(AgnocastTimer &&) = delete;

  /**
   * @brief Get the file descriptor for this timer
   *
   * @return int Timer file descriptor
   */
  int get_fd() const;

  /**
   * @brief Handle a timer event (read expiration count and execute callback)
   */
  void handle_event();

  /**
   * @brief Cancel the timer
   */
  void cancel();

  /**
   * @brief Check if timer is canceled
   *
   * @return true if canceled
   */
  bool is_canceled() const;

  /**
   * @brief Reset the timer with a new period
   *
   * @param period New timer period in nanoseconds
   * @throws std::runtime_error if timer update fails
   */
  void reset(std::chrono::nanoseconds period);

private:
  int timer_fd_;
  std::function<void()> callback_;
  bool canceled_;
};

}  // namespace agnocast
