#include <chrono>
#include <functional>
#include <stdexcept>

namespace agnocast
{

class AgnocastTimer
{
public:
  AgnocastTimer(std::chrono::nanoseconds period, std::function<void()> callback);

  ~AgnocastTimer();

  // Disable copy and move
  AgnocastTimer(const AgnocastTimer &) = delete;
  AgnocastTimer & operator=(const AgnocastTimer &) = delete;
  AgnocastTimer(AgnocastTimer &&) = delete;
  AgnocastTimer & operator=(AgnocastTimer &&) = delete;

  int get_fd() const;

  void handle_event();

  void cancel();

  bool is_canceled() const;

  void reset(std::chrono::nanoseconds period);

private:
  int timer_fd_;
  std::function<void()> callback_;
  bool canceled_;
};

}  // namespace agnocast
